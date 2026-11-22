import Mathlib
import GroundTheory.ProfiniteCohomology.CupProducts
import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
import Development.AbelianVarietyTheory.Definitions.Divisors.BlockGLMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
import GroundTheory.FunctionField.PlaceBridge
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0005
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC

def A1 : Prop := ∀ (R : Type) [CommRing R] {K L : Cx R} (f : K ⟶ L) [QuasiIso f] (F : Shv R) (n : ℤ),
  Function.Bijective (HK.pull R f F n)

def A2 : Prop := ∀ (R : Type) [CommRing R] {Y X : Scheme.{0}} (f : Y ⟶ X) [Smooth f] [Surjective f] (F : Shv R), Eqv R (cechAug f) F

def A3 : Prop := ∀ (R : Type) [CommRing R] {E E' : Spc} (f : E ⟶ E') (F : Shv R),
  (∀ n, Eqv R (disc.map (f.app n)) F) → Eqv R f F

def A4 : Prop := ∀ (R : Type) [CommRing R] {U V E U' V' E' : Spc} (f : U ⟶ E) (g : V ⟶ E) (f' : U' ⟶ E') (g' : V' ⟶ E')
  (p : E ⟶ E') (u : U ⟶ U') (v : V ⟶ V') (hu : f ≫ p = u ≫ f') (hv : g ≫ p = v ≫ g') (F : Shv R),
  Cover2 R f g → Cover2 R f' g' → Eqv R u F → Eqv R v F → Eqv R (pullback.map f g f' g' u v p hu hv) F → Eqv R p F

def A5 : Prop := ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (F : Shv R) (n : ℤ), 0 < n → ∀ x : H R (sch.obj X) F n,
  ∃ (Y : Scheme.{0}) (f : Y ⟶ X), Etale f ∧ Surjective f ∧ pull R (sch.map f) F n x = 0

def DivisorNaturality : Prop := ∀ (q : ℕ) [NeZero q],
  (∀ {E E' : Spc} (f : E ⟶ E') {n m i j : ℤ} (a : Ht q E' n i) (b : Ht q E' m j),
    pull _ f _ _ (cup q a b) = cup q (pull _ f _ _ a) (pull _ f _ _ b)) ∧
  (∀ {E E' : Spc} (f : E ⟶ E'), Inv q E' → pull _ f _ _ (one q E') = one q E) ∧
  (∀ {E E' : Spc} (f : E ⟶ E') (L : E' ⟶ ofCat (glCat 1)), Inv q E' → pull _ f _ _ (c1 q L) = c1 q (f ≫ L)) ∧
  ∀ {Y X : Scheme.{0}} (f : Y ⟶ X) (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) →
    pull _ (sch.map f) _ _ (kum q u) = kum q (Units.map f.appTop.hom.toMonoidHom u)

def DivisorRingCompatibility : Prop := ∀ (q : ℕ) [NeZero q] (E : Spc),
  (Inv q E → ∀ {n i : ℤ} (a : Ht q E n i), cup q (one q E) a = a.cast (by ring) (by ring)) ∧
  (∀ {n m k i j l : ℤ} (a : Ht q E n i) (b : Ht q E m j) (c : Ht q E k l),
    cup q (cup q a b) c = (cup q a (cup q b c)).cast (by ring) (by ring)) ∧
  ∀ {n m i j : ℤ} (a : Ht q E n i) (b : Ht q E m j), cup q a b = (n * m).negOnePow • (cup q b a).cast (by ring) (by ring)

def DivisorSupportCondition : Prop := ∀ (q : ℕ) [NeZero q] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 (ZMod q) f g →
  ∀ {n m i j : ℤ} (a : Ht q E n i) (b : Ht q E m j), pull _ f _ _ a = 0 → pull _ g _ _ b = 0 → cup q a b = 0

def DivisorAdditivity : Prop := ∀ (q : ℕ) [NeZero q],
  (∀ {E : Spc} (L M N : E ⟶ ofCat (glCat 1)), Inv q E →
    (∀ (U : Scheme.{0}) (x : Sx E 1 U), lineUnit N x = lineUnit L x * lineUnit M x) → c1 q N = c1 q L + c1 q M) ∧
  ∀ {X : Scheme.{0}} (u v : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) → kum q (u * v) = kum q u + kum q v ∧ kum q (u ^ q) = 0

def A7 : Prop := ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R)), S.ShortExact →
  ∃ z : Cocycle (res R S.X₃) (res R S.X₁) 1, ∀ (K : Cx R) (n : ℤ),
    Function.Exact (HK.post R K S.f n) (HK.post R K S.g n) ∧
    Function.Exact (HK.post R K S.g n) (HK.ext R K z n (n + 1) rfl) ∧
    Function.Exact (HK.ext R K z n (n + 1) rfl) (HK.post R K S.f (n + 1))

def A8 : Prop := ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (E : Spc) (F : Shv S) (n : ℤ),
  Function.Bijective (restrH φ E F n)

def A9 : Prop := ∀ (R : Type) [CommRing R] (F : Shv R), (∀ (E : Spc) (n : ℤ), n < 0 → Subsingleton (H R E F n)) ∧
  ∃ e : ∀ X : Scheme.{0}, Sec F X ≃+ H R (sch.obj X) F 0,
    (∀ {Y X : Scheme.{0}} (f : Y ⟶ X) (s : Sec F X), pull R (sch.map f) F 0 (e X s) = e Y (Sec.res f s)) ∧
    ∀ (X : Scheme.{0}) (s : Sec F X), ∃ α : Cocycle _ _ 0, CohomologyClass.mk α = e X s ∧
      ev α.1 0 0 (by simp) X (𝟙 X) = Sec.map (resι R F) s

def A10 : Prop := ∀ (R : Type) [CommRing R] (E : Spc) {F G : Shv R} (φ : F ⟶ G),
  (∀ U : Scheme.{0}, Nonempty (Sx E 0 U) → Function.Bijective (Sec.map φ (U := U))) →
  ∀ n, Function.Bijective (HK.post R ((chains R).obj E) φ n)

def A11 : Prop := ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ E : Spc,
  (∀ {n m i j : ℤ} (a : Ht Q E n i) (b : Ht Q E m j), red Q q E _ _ (cup Q a b) = cup q (red Q q E _ _ a) (red Q q E _ _ b)) ∧
  (Inv Q E → red Q q E _ _ (one Q E) = one q E ∧ ∀ L : E ⟶ ofCat (glCat 1), red Q q E _ _ (c1 Q L) = c1 q L) ∧
  (∀ (n i : ℤ) (a : Ht Q E n i), red Q Q E n i a = a) ∧
  ∀ r : ℕ, r ∣ q → ∀ (n i : ℤ) (a : Ht Q E n i), red q r E n i (red Q q E n i a) = red Q r E n i a

def B1 : Prop := ∀ (q : ℕ) {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c →
  ∀ n i : ℤ,
  (∀ x : Ht q (sp c.pt) n i, IsUnit (q : c.pt) → ∃ j y, pull _ (spMap (c.ι.app j).hom) _ _ y = x) ∧
  ∀ j (y : Ht q (sp (D.obj j)) n i), IsUnit (q : D.obj j) → pull _ (spMap (c.ι.app j).hom) _ _ y = 0 →
    ∃ (k : J) (f : j ⟶ k), pull _ (spMap (D.map f).hom) _ _ y = 0

def B2 : Prop := ∀ (R : Type) [CommRing R] (A : Type) [CommRing A], SH A → ∀ (F : Shv R) (n : ℤ), 0 < n →
  Subsingleton (H R (sp A) F n)

def B3 : Prop := ∀ (q : ℕ) {Y X S : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) [QuasiCompact p] [QuasiSeparated p] [QuasiCompact f]
  [QuasiSeparated f], IsUnit (q : Γ(S, ⊤)) → ∀ i : ℤ,
  (∀ (A : Type) [CommRing A] (s : Spec (CommRingCat.of A) ⟶ S), SH A →
    Eqv _ (sch.map (pullback.map (f ≫ p) s p s f (𝟙 _) (𝟙 _) (by simp) (by simp))) (tw q i)) → Eqv _ (sch.map f) (tw q i)

def B4 : Prop := ∀ (q : ℕ) {Y X : Scheme.{0}} (f : Y ⟶ X) [IsIntegralHom f] [Surjective f], IsUnit (q : Γ(X, ⊤)) → ∀ i : ℤ,
  Eqv _ (cechAug f) (tw q i)

def B5 : Prop := ∀ (q : ℕ) (A : Type) [CommRing A] [IsDomain A], AIC A → IsUnit (q : A) → Acyc q (sp A)

def DivisorPicardCompatibility : Prop := ∀ (A : Type) [CommRing A], Nonempty (H ℤ (sp A) Gm 1 ≃+ Additive (CommRing.Pic A))

def B6h1 : Prop := ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], IsUnit (q : A) → (∀ u : Aˣ, ∃ v, u = v ^ q) →
  (∀ c : CommRing.Pic A, c ^ q = 1 → c = 1) → Subsingleton (Ht q (sp A) 1 1)

def B7 : Prop := ∀ (q : ℕ) [NeZero q] (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω], IsUnit (q : K) → ∀ (i : ℕ)
  (M : Rep (ZMod q) (Ω ≃ₐ[K] Ω)) [GroundTheory.ProfCoh.IsDiscreteRep M] (ζ : Ω), IsPrimitiveRoot ζ q → ∀ b : Module.Basis Unit (ZMod q) M,
  (∀ (σ : Ω ≃ₐ[K] Ω) (a : ℕ), σ ζ = ζ ^ a → M.ρ σ (b ()) = ((a : ZMod q) ^ i) • b ()) → ∀ n : ℕ,
  Nonempty (Ht q (sp K) n i ≃+ GroundTheory.ProfCoh.cohomology M n)

def C1 : Prop := ∀ (q : ℕ) [NeZero q] (k K : Type) [Field k] [IsAlgClosed k] [Field K] [Algebra (RatFunc k) K]
  [Algebra.IsAlgebraic (RatFunc k) K], IsUnit (q : K) → ∀ n i : ℤ, 2 ≤ n → Subsingleton (Ht q (sp K) n i)

def C2 : Prop := ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B]
  [Algebra.FiniteType k B], IsUnit (q : k) → ∀ n i : ℤ, 2 ≤ n → Subsingleton (Ht q (sp B) n i)

def C3 : Prop := ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) →
  ∀ (B : Type) [CommRing B] [Algebra (Polynomial T) B] [Algebra.Etale (Polynomial T) B] [Algebra T B]
    [IsScalarTower T (Polynomial T) B] (i : ℤ),
  Eqv _ (spMap (Algebra.TensorProduct.includeRight (R := T) (A := FractionRing T) (B := B)).toRingHom) (tw q i)

def C4 : Prop := ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], IsUnit (q : A) → ∀ i : ℤ,
  Eqv _ (spMap (Polynomial.C : A →+* Polynomial A)) (tw q i)

def C5 : Prop := ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ n i : ℤ,
  (2 ≤ n → Subsingleton (Ht q (sp (LaurentPolynomial A)) n i)) ∧ Nonempty (Ht q (sp (LaurentPolynomial A)) 1 i ≃+ ZMod q)

def D1 : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)), Inv q E → ∀ n i : ℤ,
  Function.Bijective fun a : ∀ j : Fin N, Ht q E (n - 2 * (j : ℕ)) (i - (j : ℕ)) =>
    ∑ j : Fin N, ((cup q (pull _ (pullback.fst V (PGL.pr N)) _ _ (a j))
      (cpow q (c1 q (pullback.snd V (PGL.pr N) ≫ PGL.line N)) j)).cast (by ring) (by ring) : Ht q _ n i)

def D2 : Prop := ∀ (q : ℕ) [NeZero q] (k : ℕ), 0 < k →
  ∃ s : ∀ {E : Spc} {N : ℕ}, (E ⟶ ofCat (glCat N)) → Ht q E (2 * k) k,
    (∀ {E E' : Spc} {N} (f : E ⟶ E') (V : E' ⟶ ofCat (glCat N)), Inv q E' → pull _ f _ _ (s V) = s (f ≫ V)) ∧
    (∀ {E : Spc} {a b} (V : E ⟶ ofCat (glCat a)) (W : E ⟶ ofCat (glCat b)), Inv q E → s (bsumOf V W) = s V + s W) ∧
    ∀ {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E → s L = cpow q (c1 q L) k

def D3 : Prop := ∀ (R : Type) [CommRing R] (Γ : Type) [Group Γ] (X : Scheme.{0}) (m : ℕ),
  (∀ c : groupHomology.cycles (Rep.trivial R Γ R) m, ∃ z, IsSlant R X (groupHomology.iCycles (Rep.trivial R Γ R) m c) z) ∧
  ∀ (F : Shv R) (n : ℤ), IsSlantMap R Γ X F m n (slantR R Γ X F m n)

def E1 : Prop := ∀ (q : ℕ) (A : Type) [CommRing A] (I : Ideal A) [HenselianRing A I], IsUnit (q : A) → ∀ i : ℤ,
  Eqv _ (spMap (Ideal.Quotient.mk I)) (tw q i)

def E2 : Prop := ∀ (q : ℕ) (A : Type) [CommRing A] [IsLocalRing A], SH A → IsUnit (q : A) → ∀ {X : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of A)) [IsProper p] (i : ℤ),
  Eqv _ (sch.map (pullback.fst p (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))) (tw q i)

def E3 : Prop := ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) →
  ∀ {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of T)) [Smooth p] (i : ℤ),
  Eqv _ (sch.map (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap T (FractionRing T)))))) (tw q i)

def E4 : Prop := ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) → ∀ {X : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p] (n i : ℤ), Finite (Ht q (sch.obj X) n i)

def E6 : Prop := ∀ (q : ℕ) [NeZero q] {X Z S : Scheme.{0}} (p : X ⟶ S) (ι : Z ⟶ X) [IsClosedImmersion ι] (d e : ℕ)
  [SmoothOfRelativeDimension (e + d) p] [SmoothOfRelativeDimension e (ι ≫ p)], IsUnit (q : Γ(S, ⊤)) →
  ∀ U : X.Opens, (U : Set X) = (Set.range ι)ᶜ → ∀ n i : ℤ,
  (n < 2 * d - 1 → Function.Bijective (pull _ (sch.map U.ι) (tw q i) n)) ∧
  (n < 2 * d → Function.Injective (pull _ (sch.map U.ι) (tw q i) n))

def E8 : Prop := ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) → ∀ {X : Scheme.{0}} [IsIntegral X]
  (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p] (d : ℕ) [SmoothOfRelativeDimension d p],
  ∃ tr : Ht q (sch.obj X) (2 * d) d ≃+ ZMod q, ∀ (n i : ℤ) (φ : Ht q (sch.obj X) (2 * d - n) (d - i) →+ ZMod q),
    ∃! a : Ht q (sch.obj X) n i, ∀ b, φ b = tr ((cup q a b).cast (by ring) (by ring))

end GlobalTheory.EtC

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IdTower
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.GalV

structure HTower (k : Type) [Field k] where
  Γ : Type
  Z : Scheme.{0}
  q : Z ⟶ Spec (CommRingCat.of k)
  Y : Γ → Scheme.{0}
  s : ∀ g, Y g ⟶ Z
  t : ∀ g, Y g ⟶ Z
  comm : ∀ g, t g ≫ q = s g ≫ q

variable {k : Type} [Field k] (l : ℕ) [Fact l.Prime] (H : HTower k) (Ω : Type) [Field Ω] [Algebra k Ω]

abbrev HTower.geomZ : Scheme.{0} := GlobalTheory.Et.geom Ω H.q

def HTower.sΩ (g : H.Γ) : GlobalTheory.Et.geom Ω (H.s g ≫ H.q) ⟶ H.geomZ Ω := GlobalTheory.Et.geomMap Ω (H.s g ≫ H.q) (H.s g) rfl

def HTower.tΩ (g : H.Γ) : GlobalTheory.Et.geom Ω (H.s g ≫ H.q) ⟶ H.geomZ Ω := GlobalTheory.Et.geomMap Ω (H.s g ≫ H.q) (H.t g) (H.comm g)

open Classical in

def hop (g : H.Γ) : Htot l (sch.obj (H.geomZ Ω)) →ₗ[ℚ_[l]] Htot l (sch.obj (H.geomZ Ω)) :=
  if h : ∃ T, IsCorrOp l (H.sΩ Ω g) (H.tΩ Ω g) T then h.choose else 0

def V (L : Type) [Field L] [Algebra ℚ_[l] L] {J : Type} (ι : J → H.Γ) (θ : J → L) :
    Submodule L (TensorProduct ℚ_[l] L (Htot l (sch.obj (H.geomZ Ω)))) :=
  genEig L (fun j => hop l H Ω (ι j)) θ

def galV (L : Type) [Field L] [Algebra ℚ_[l] L] (σ : Ω ≃ₐ[k] Ω) :
    TensorProduct ℚ_[l] L (Htot l (sch.obj (H.geomZ Ω))) →ₗ[L] TensorProduct ℚ_[l] L (Htot l (sch.obj (H.geomZ Ω))) :=
  (galTot l Ω H.q σ).baseChange L

def HTower.triv (k : Type) [Field k] : HTower k where
  Γ := Empty
  Z := Spec (CommRingCat.of k)
  q := 𝟙 _
  Y := fun g => g.elim
  s := fun g => g.elim
  t := fun g => g.elim
  comm := fun g => g.elim

def HTower.idTower (k : Type) [Field k] : HTower k where
  Γ := Unit
  Z := Spec (CommRingCat.of k)
  q := 𝟙 _
  Y := fun _ => Spec (CommRingCat.of k)
  s := fun _ => 𝟙 _
  t := fun _ => 𝟙 _
  comm := fun _ => rfl

end GlobalTheory.GalV

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne
section
set_option autoImplicit false

noncomputable section

open scoped IntermediateField Polynomial

namespace GlobalTheory.Nef

def IsFF (k F : Type) [Field k] [Field F] [Algebra k F] : Prop :=
  ∃ t : F, Transcendental k t ∧ FiniteDimensional k⟮t⟯ F

def Place (k F : Type) [Field k] [Field F] [Algebra k F] : Type :=
  {v : Valuation F (WithZero (Multiplicative ℤ)) //
    Function.Surjective v ∧ ∀ c : k, c ≠ 0 → v (algebraMap k F c) = 1}

variable {k F : Type} [Field k] [Field F] [Algebra k F]

abbrev Place.O (v : Place k F) : ValuationSubring F := v.1.valuationSubring

def ord (v : Place k F) (x : F) : ℤ := -WithZero.log (v.1 x)

def nrm {n : ℕ} (v : Place k F) (x : Fin n → F) : WithZero (Multiplicative ℤ) :=
  Finset.univ.sup fun i => v.1 (x i)

def ordVec {n : ℕ} (v : Place k F) (x : Fin n → F) : ℤ := -WithZero.log (nrm v x)

def Unimod {n : ℕ} (v : Place k F) (g : Matrix (Fin n) (Fin n) F) : Prop :=
  (∀ i j, v.1 (g i j) ≤ 1) ∧ v.1 g.det = 1

def admitted {n : ℕ} (g : Place k F → Matrix (Fin n) (Fin n) F) : Prop :=
  (∀ v, (g v).det ≠ 0) ∧ {v | ¬ Unimod v (g v)}.Finite

def deg [IsAlgClosed k] {n : ℕ} (g : Place k F → Matrix (Fin n) (Fin n) F) : ℤ := ∑ᶠ v, ord v (g v).det

def degLine [IsAlgClosed k] {n : ℕ} (g : Place k F → Matrix (Fin n) (Fin n) F) (w : Fin n → F) : ℤ :=
  ∑ᶠ v, ordVec v ((g v).mulVec w)

def IsRes {E : Type} [Field E] [Algebra k E] [Algebra F E] (ρ : Place k E → Place k F) : Prop :=
  ∀ p x, p.1 (algebraMap F E x) ≤ 1 ↔ (ρ p).1 x ≤ 1

def pullAd {n : ℕ} {E : Type} [Field E] [Algebra k E] [Algebra F E] (ρ : Place k E → Place k F)
    (g : Place k F → Matrix (Fin n) (Fin n) F) : Place k E → Matrix (Fin n) (Fin n) E :=
  fun p => (g (ρ p)).map (algebraMap F E)

def LinesLE [IsAlgClosed k] {n : ℕ} (g : Place k F → Matrix (Fin n) (Fin n) F) (b : ℝ) : Prop :=
  ∀ (E : Type) [Field E] [Algebra k E] [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E]
    (ρ : Place k E → Place k F), IsRes ρ → ∀ w : Fin n → E, w ≠ 0 →
      (degLine (pullAd ρ g) w : ℝ) ≤ b * Module.finrank F E

def IsRat (φ : PowerSeries F) : Prop :=
  ∃ p q : F[X], q ≠ 0 ∧ (q : PowerSeries F) * φ = (p : PowerSeries F)

def hankel (c : ℕ → F) (n : ℕ) : F := (Matrix.of fun i j : Fin (n + 1) => c (i + j)).det

def sc (v : Place k F) (u : F) : PowerSeries v.O →+* PowerSeries F :=
  (PowerSeries.rescale u).comp (PowerSeries.map v.O.subtype)

namespace Lib

open scoped WithZero
open IsDedekindDomain GroundTheory.FunctionField

theorem isFF_iff : IsFF k F ↔ IsFunctionField k F := ⟨fun h => ⟨h⟩, fun h => h.1⟩

def toRing (v : Nef.Place k F) : GroundTheory.FunctionField.Place k F where
  ring := v.1.valuationSubring
  ne_top h := by
    obtain ⟨x, hx⟩ := v.2.1 (WithZero.exp 1)
    have hm : x ∈ v.1.valuationSubring := h ▸ ValuationSubring.mem_top _
    rw [Valuation.mem_valuationSubring_iff, hx, ← WithZero.exp_zero, WithZero.exp_le_exp] at hm
    omega
  algebraMap_mem c := by
    rw [Valuation.mem_valuationSubring_iff]
    by_cases hc : c = 0
    · simp [hc]
    · exact (v.2.2 c hc).le

theorem valuation_toRing [IsFunctionField k F] (v : Nef.Place k F) : (toRing v).valuation = v.1 :=
  valuation_eq_of_isEquiv (Valuation.isEquiv_iff_val_le_one.2 fun {x} => (toRing v).valuation_le_one_iff x)
    (toRing v).valuation_surjective v.2.1

def placeEquiv [IsFunctionField k F] : Nef.Place k F ≃ GroundTheory.FunctionField.Place k F where
  toFun := toRing
  invFun w := ⟨w.valuation, w.valuation_surjective, fun _ hc => w.valuation_algebraMap' hc⟩
  left_inv v := Subtype.ext (valuation_toRing v)
  right_inv w := GroundTheory.FunctionField.Place.ext (by
    ext x
    exact w.valuation_le_one_iff x)

theorem ord_toRing [IsFunctionField k F] (v : Nef.Place k F) (x : F) : (toRing v).ord x = ord v x := by
  rw [GroundTheory.FunctionField.Place.ord, valuation_toRing, ord]

open scoped Classical in

def atPlace {n : ℕ} (v : Nef.Place k F) (d : Fin n → F) : Nef.Place k F → Matrix (Fin n) (Fin n) F :=
  fun u => if u = v then Matrix.diagonal d else 1

section Line

variable (k)

open scoped Classical in

def atInf : Nef.Place k (RatFunc k) :=
  ⟨RatFunc.inftyValuation k, fun y => by
    rcases eq_or_ne y 0 with rfl | hy
    · exact ⟨0, map_zero _⟩
    · exact ⟨RatFunc.X ^ WithZero.log y, by rw [RatFunc.inftyValuation.X_zpow, WithZero.exp_log hy]⟩,
    fun c hc => RatFunc.inftyValuation.C k hc⟩

variable {k}

def atPrime (u : HeightOneSpectrum k[X]) : Nef.Place k (RatFunc k) :=
  ⟨u.valuation (RatFunc k), u.valuation_surjective _, fun c hc => by
    rw [IsScalarTower.algebraMap_apply k k[X] (RatFunc k)]
    exact (u.valuation_of_algebraMap _).trans (HeightOneSpectrum.intValuation_eq_one_iff.2 fun hm =>
      u.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hm ((IsUnit.mk0 c hc).map _)))⟩

def primeOf {f : k[X]} (hf : Irreducible f) : HeightOneSpectrum k[X] where
  asIdeal := Ideal.span {f}
  isPrime := (Ideal.span_singleton_prime hf.ne_zero).2 hf.prime
  ne_bot := by simpa using hf.ne_zero

def placeX (k : Type) [Field k] : Nef.Place k (RatFunc k) := atPrime (primeOf (Polynomial.irreducible_X (R := k)))

end Line

section Product

theorem sum_ramificationIdx [IsAlgClosed k] {E : Type} [Field E] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
    [IsFunctionField k F] [IsFunctionField k E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
    (v : GroundTheory.FunctionField.Place k F) :
    ∑ w ∈ (v.finite_liesOver (K' := E)).toFinset, w.ramificationIdx v = Module.finrank F E := by
  rw [← v.sum_ramificationIdx_mul_inertiaDeg (K' := E)]
  refine Finset.sum_congr rfl fun w _ => ?_
  have d1 : v.deg = 1 := by
    have : Algebra.IsIntegral k v.ResidueField := Algebra.IsIntegral.of_finite _ _
    exact (LinearEquiv.ofBijective (Algebra.linearMap k v.ResidueField)
      IsAlgClosed.algebraMap_bijective_of_isIntegral).finrank_eq.symm.trans (Module.finrank_self k)
  have d2 : w.deg = 1 := by
    have : Algebra.IsIntegral k w.ResidueField := Algebra.IsIntegral.of_finite _ _
    exact (LinearEquiv.ofBijective (Algebra.linearMap k w.ResidueField)
      IsAlgClosed.algebraMap_bijective_of_isIntegral).finrank_eq.symm.trans (Module.finrank_self k)
  simp [GroundTheory.FunctionField.Place.inertiaDeg, d1, d2]

end Product

end Lib

end GlobalTheory.Nef
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.JmMulJm
section
noncomputable section

open scoped Matrix.Norms.L2Operator
open ReciprocityTheory.ChartRestriction.DS Matrix

namespace GlobalTheory.Kg

variable {T : Type} [Fintype T] [DecidableEq T] {n : ℕ}

abbrev MatT (T : Type) (n : ℕ) : Type := T → Matrix (Fin n) (Fin n) ℂ

def UJfam (ε : T → Fin n → Bool) : Subgroup (MatT T n)ˣ where
  carrier := {g | ∀ τ, (g.val τ)ᴴ * Jm (ε τ) * g.val τ = Jm (ε τ)}
  one_mem' τ := by simp
  mul_mem' {g h} hg hh τ := by
    simp only [Units.val_mul, Pi.mul_apply, Matrix.conjTranspose_mul]
    calc (h.val τ)ᴴ * (g.val τ)ᴴ * Jm (ε τ) * (g.val τ * h.val τ)
        = (h.val τ)ᴴ * ((g.val τ)ᴴ * Jm (ε τ) * g.val τ) * h.val τ := by simp only [Matrix.mul_assoc]
      _ = Jm (ε τ) := by rw [hg τ, hh τ]
  inv_mem' {g} hg τ := by
    have h1 : g.val τ * (g⁻¹).val τ = 1 := by
      rw [← Pi.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one, Pi.one_apply]
    calc ((g⁻¹).val τ)ᴴ * Jm (ε τ) * (g⁻¹).val τ
        = ((g⁻¹).val τ)ᴴ * ((g.val τ)ᴴ * Jm (ε τ) * g.val τ) * (g⁻¹).val τ := by rw [hg τ]
      _ = (g.val τ * (g⁻¹).val τ)ᴴ * Jm (ε τ) * (g.val τ * (g⁻¹).val τ) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Jm (ε τ) := by rw [h1]; simp

def uJfam (ε : T → Fin n → Bool) : Submodule ℝ (MatT T n) where
  carrier := {X | ∀ τ, (X τ)ᴴ * Jm (ε τ) + Jm (ε τ) * X τ = 0}
  add_mem' {X Y} hX hY τ := by
    simp only [Pi.add_apply, Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
    calc (X τ)ᴴ * Jm (ε τ) + (Y τ)ᴴ * Jm (ε τ) + (Jm (ε τ) * X τ + Jm (ε τ) * Y τ)
        = ((X τ)ᴴ * Jm (ε τ) + Jm (ε τ) * X τ) + ((Y τ)ᴴ * Jm (ε τ) + Jm (ε τ) * Y τ) := by abel
      _ = 0 := by rw [hX τ, hY τ, add_zero]
  zero_mem' τ := by simp
  smul_mem' c X hX τ := by
    have h : ((c • X) τ) = (c : ℂ) • X τ := by ext; simp
    rw [h, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul]
    have hs : star (c : ℂ) = (c : ℂ) := Complex.conj_ofReal c
    rw [hs, ← smul_add]
    simp [hX τ]

def reU (ε : T → Fin n → Bool) (τ : T) (a b : Fin n) : MatT T n :=
  fun σ => if σ = τ then (1 / 2 : ℂ) • (Matrix.single a b 1 - Jm (ε τ) * (Matrix.single a b 1)ᴴ * Jm (ε τ)) else 0

def imU (ε : T → Fin n → Bool) (τ : T) (a b : Fin n) : MatT T n :=
  fun σ => if σ = τ then (-Complex.I / 2) • (Matrix.single a b 1 + Jm (ε τ) * (Matrix.single a b 1)ᴴ * Jm (ε τ)) else 0

end GlobalTheory.Kg

end
end


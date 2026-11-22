import Development.EtaleCohomology.TateTwists.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.EtaleCohomology.TateTwists.Bundle0005
import Development.EtaleCohomology.TateTwists.Bundle0002
import Development.EtaleCohomology.TateTwists.Bundle0003

-- bundled from Development.EtaleCohomology.TateTwists.EtaleTensorUniversalPropertyOfDegreewise
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.TensUnivPf

theorem sec_eq_zero_of_isZero {R : Type} [CommRing R] {F : Shv R} (hF : IsZero F) {U : Scheme.{0}} (x : Sec F U) : x = 0 := by
  have h1 : (𝟙 F : F ⟶ F) = 0 := hF.eq_of_src _ _
  have := congrArg (fun φ : F ⟶ F => (φ.hom.app (op U)).hom x) h1
  simpa using this

theorem secMap_comp {R : Type} [CommRing R] {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

def postPair {R : Type} [CommRing R] {I J K K' : Cx R} (μ : Pair I J K) (u : K ⟶ K') : Pair I J K' where
  mul U s t w h := (μ.mul U s t w h).compr₂ ((u.f w).hom.app (op U)).hom
  nat g s t w h a b := by
    simp only [LinearMap.compr₂_apply]
    rw [← μ.nat g s t w h a b]
    exact (congrArg (fun φ => (ModuleCat.Hom.hom φ) (μ.mul _ s t w h a b)) ((u.f w).hom.naturality g.op)).symm
  leibniz U s t w h a b := by
    simp only [LinearMap.compr₂_apply]
    have hc : Sec.map (K'.d w (w+1)) (Sec.map (u.f w) (μ.mul U s t w h a b)) = Sec.map (u.f (w+1)) (Sec.map (K.d w (w+1)) (μ.mul U s t w h a b)) := by
      rw [← secMap_comp, ← secMap_comp, u.comm]
    change Sec.map (K'.d w (w+1)) (Sec.map (u.f w) (μ.mul U s t w h a b)) = _
    rw [hc, μ.leibniz]
    simp [map_add]

theorem part3 {R : Type} [CommRing R] {I J K : Cx R} (τ : Pair I J K) {K' : Cx R} (u : K ⟶ K') :
    ∃ ν : Pair I J K', τ.Compat ν (𝟙 I) (𝟙 J) u :=
  ⟨postPair τ u, fun U s t w h a b => rfl⟩

theorem sep {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (S : Sieve U) (hS : S ∈ Scheme.etaleTopology U)
    (y z : Sec F U) (h : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec.res g y = Sec.res g z) : y = z := by
  have h1 := (isSheaf_iff_isSheaf_of_type _ _).1
    ((Presheaf.isSheaf_iff_isSheaf_forget _ F.obj (forget (ModuleCat.{1} (ULift.{1} R)))).1 F.cond)
  exact (h1 S hS).isSeparatedFor.ext (fun V g hg => h V g hg)

theorem sep_loc {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (y z : Sec F U)
    (h : Loc U fun V g => Sec.res g y = Sec.res g z) : y = z := by
  obtain ⟨S, hS, hh⟩ := h
  exact sep S hS y z hh

theorem isZero_of_sec {R : Type} [CommRing R] {F : Shv R} (h : ∀ (U : Scheme.{0}) (x : Sec F U), x = 0) : IsZero F := by
  rw [IsZero.iff_id_eq_zero]
  ext U x
  exact (h _ _).trans (h _ _).symm

theorem lift_ind {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) (V : Scheme.{0}) (w : ℤ)
    (P : Sec (K.X w) V → Prop) (h0 : P 0) (hadd : ∀ a b, P a → P b → P (a + b))
    (hm : ∀ (s t : ℤ) (h : s + t = w) (a : Sec (I.X s) V) (b : Sec (J.X t) V), P (μ.mul V s t w h a b))
    (x : Tens I J V w) : P (μ.lift V w x) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simpa using h0
  | of p t =>
    simp only [Pair.lift]
    rw [← DirectSum.lof_eq_of (ULift.{1} R), DirectSum.toModule_lof]
    induction t using TensorProduct.induction_on with
    | zero => simpa using h0
    | tmul a b => simpa using hm p.1.1 p.1.2 p.2 a b
    | add a b ha hb => rw [map_add]; exact hadd _ _ ha hb
  | add a b ha hb => rw [map_add]; exact hadd _ _ ha hb

theorem part2 {R : Type} [CommRing R] {I J K : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor) :
    I.IsStrictlyGE 0 → J.IsStrictlyGE 0 → K.IsStrictlyGE 0 := by
  intro hI hJ
  rw [CochainComplex.isStrictlyGE_iff]
  intro w hw
  apply isZero_of_sec
  intro U y
  apply sep_loc
  obtain ⟨S, hS, hh⟩ := hτ.1 U w y
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨x, hx⟩ := hh V g hg
  rw [← hx]
  simp only [map_zero]
  refine lift_ind τ V w (fun z => z = 0) rfl (fun a b ha hb => by rw [ha, hb]; simp) ?_ x
  intro s t h a b
  rcases (show s < 0 ∨ t < 0 by omega) with hs | ht
  · rw [sec_eq_zero_of_isZero (I.isZero_of_isStrictlyGE 0 s hs) a]; simp
  · rw [sec_eq_zero_of_isZero (J.isZero_of_isStrictlyGE 0 t ht) b]; simp

theorem uniq {R : Type} [CommRing R] {I J K : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor)
    {I' J' K' : Cx R} (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J') (u v : K ⟶ K')
    (hu : τ.Compat ν f g u) (hv : τ.Compat ν f g v) : u = v := by
  ext w U y
  obtain ⟨U⟩ := U
  change Sec.map (u.f w) y = Sec.map (v.f w) y
  apply sep_loc
  obtain ⟨S, hS, hh⟩ := hτ.1 U w y
  refine ⟨S, hS, fun V e he => ?_⟩
  obtain ⟨x, hx⟩ := hh V e he
  have nu : ∀ (φ : K ⟶ K') (z : Sec (K.X w) U), Sec.res e (Sec.map (φ.f w) z) = Sec.map (φ.f w) (Sec.res e z) :=
    fun φ z => (congrArg (fun ψ => (ModuleCat.Hom.hom ψ) z) ((φ.f w).hom.naturality e.op)).symm
  rw [nu, nu, ← hx]
  refine lift_ind τ V w (fun z => Sec.map (u.f w) z = Sec.map (v.f w) z) (by simp) ?_ ?_ x
  · intro a b ha hb
    simp only [Sec.map, map_add] at ha hb ⊢
    rw [ha, hb]
  · intro s t h a b
    rw [hu, hv]

theorem nat_sec {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (e : V ⟶ U) (z : Sec F U) :
    Sec.res e (Sec.map φ z) = Sec.map φ (Sec.res e z) :=
  (congrArg (fun ψ => (ModuleCat.Hom.hom ψ) z) (φ.hom.naturality e.op)).symm

theorem secMap_add {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map φ (a + b) = Sec.map φ a + Sec.map φ b := map_add _ a b

theorem secMap_zsmul {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (n : ℤˣ) (a : Sec F U) :
    Sec.map φ (n • a) = n • Sec.map φ a := by
  rw [Units.smul_def, Units.smul_def]; exact map_zsmul _ _ a

theorem exists_of_degreewise {R : Type} [CommRing R] {I J K : Cx R} (τ : Pair I J K) (hτ : τ.IsTensor)
    {I' J' K' : Cx R} (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J') (m : ∀ w, K.X w ⟶ K'.X w)
    (hm : ∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
      Sec.map (m w) (τ.mul U s t w h a b) = ν.mul U s t w h (Sec.map (f.f s) a) (Sec.map (g.f t) b)) :
    ∃ u : K ⟶ K', τ.Compat ν f g u := by
  refine ⟨{ f := m, comm' := ?_ }, fun U s t w h a b => hm U s t w h a b⟩
  rintro w _ rfl
  ext U y
  obtain ⟨U⟩ := U
  change Sec.map (K'.d w (w+1)) (Sec.map (m w) y) = Sec.map (m (w+1)) (Sec.map (K.d w (w+1)) y)
  apply sep_loc
  obtain ⟨S, hS, hh⟩ := hτ.1 U w y
  refine ⟨S, hS, fun V e he => ?_⟩
  obtain ⟨x, hx⟩ := hh V e he
  rw [nat_sec, nat_sec, nat_sec, nat_sec, ← hx]
  refine lift_ind τ V w (fun z => Sec.map (K'.d w (w+1)) (Sec.map (m w) z) = Sec.map (m (w+1)) (Sec.map (K.d w (w+1)) z))
    (by simp [Sec.map]) ?_ ?_ x
  · intro a b ha hb
    simp only [secMap_add] at ha hb ⊢
    rw [ha, hb]
  · intro s t h a b
    have cf : Sec.map (f.f (s+1)) (Sec.map (I.d s (s+1)) a) = Sec.map (I'.d s (s+1)) (Sec.map (f.f s) a) := by
      rw [← secMap_comp, ← secMap_comp, f.comm]
    have cg : Sec.map (g.f (t+1)) (Sec.map (J.d t (t+1)) b) = Sec.map (J'.d t (t+1)) (Sec.map (g.f t) b) := by
      rw [← secMap_comp, ← secMap_comp, g.comm]
    rw [hm, τ.leibniz, secMap_add, secMap_zsmul, hm, hm, ν.leibniz, cf, cg]

end LateralTheory.EtaleFoundations.TensUnivPf

def LateralTheory.EtaleFoundations.EtaleTensorDegreewiseMapExists : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor →
    ∀ {I' J' K' : Cx R} (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J') (w : ℤ),
      ∃ m : K.X w ⟶ K'.X w, ∀ (U : Scheme.{0}) (s t : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
        Sec.map m (τ.mul U s t w h a b) = ν.mul U s t w h (Sec.map (f.f s) a) (Sec.map (g.f t) b)

theorem LateralTheory.EtaleFoundations.etale_tensor_universal_property_of_degreewise (hdeg : LateralTheory.EtaleFoundations.EtaleTensorDegreewiseMapExists) :
    LateralTheory.EtaleFoundations.EtaleTensorPairUniversalProperty := by
  intro R _ I J K τ hτ
  refine ⟨fun {I' J' K'} ν f g => ?_, LateralTheory.EtaleFoundations.TensUnivPf.part2 τ hτ,
    fun u => LateralTheory.EtaleFoundations.TensUnivPf.part3 τ u⟩
  obtain ⟨u, hu⟩ := LateralTheory.EtaleFoundations.TensUnivPf.exists_of_degreewise τ hτ ν f g
    (fun w => (hdeg R τ hτ ν f g w).choose) (fun U s t w h a b => (hdeg R τ hτ ν f g w).choose_spec U s t h a b)
  exact ⟨u, hu, fun v hv => LateralTheory.EtaleFoundations.TensUnivPf.uniq τ hτ ν f g v u hv hu⟩
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleTwistedCupAssocOfTwistedPairingExistsAssoc
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def t_twpair_ex : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j : ℤ), ∃ μ : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q (i + j))), IsTwPair μ

def t_pair_assoc : Prop :=
  ∀ (q : ℕ) [NeZero q] (E : Spc) {i j l k₁ k₂ k : ℤ} (_ : i + j = k₁) (_ : j + l = k₂) (_ : i + k₂ = k)
    (μ₁ : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q k₁)))
    (μ₂ : Pair (res _ (tw q k₁)) (res _ (tw q l)) (res _ (tw q k)))
    (ν₁ : Pair (res _ (tw q j)) (res _ (tw q l)) (res _ (tw q k₂)))
    (ν₂ : Pair (res _ (tw q i)) (res _ (tw q k₂)) (res _ (tw q k))),
    IsTwPair μ₁ → IsTwPair μ₂ → IsTwPair ν₁ → IsTwPair ν₂ →
    ∀ {n m p s₁ s₂ s : ℤ} (h₁ : n + m = s₁) (h₂ : s₁ + p = s) (h₃ : m + p = s₂) (h₄ : n + s₂ = s)
      (a : Ht q E n i) (b : Ht q E m j) (c : Ht q E p l),
      μ₂.cup E h₂ (μ₁.cup E h₁ a b) c = ν₂.cup E h₄ a (ν₁.cup E h₃ b c)

theorem cast_pair_cup {q : ℕ} {E : Spc} {i j k k' n m s s' : ℤ}
    (μ : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q k))) (e : k = k') (hk : n + m = s) (hs : s = s')
    (a : Ht q E n i) (b : Ht q E m j) :
    Ht.cast hs e (μ.cup E hk a b : Ht q E s k) = (e ▸ μ : Pair _ _ (res _ (tw q k'))).cup E (hk.trans hs) a b := by
  subst e; subst hs; rfl

theorem isTwPair_cast {q : ℕ} {i j k k' : ℤ}
    (μ : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q k))) (e : k = k') (h : IsTwPair μ) :
    IsTwPair (e ▸ μ : Pair _ _ (res _ (tw q k'))) := by
  subst e; exact h

theorem etale_twisted_cup_assoc_of_twisted_pairing_exists_assoc (hex : t_twpair_ex) (has : t_pair_assoc) : EtaleTwistedCupProductAssociative := by
  intro q _ E n m k i j l a b c
  have hp : ∀ i j : ℤ, IsTwPair (twPair q i j) := fun i j => pick_spec (hex q i j)
  have e : i + (j + l) = i + j + l := by ring
  have hs : n + (m + k) = n + m + k := by ring
  show (twPair q (i + j) l).cup E rfl ((twPair q i j).cup E rfl a b) c =
    Ht.cast hs e ((twPair q i (j + l)).cup E rfl a ((twPair q j l).cup E rfl b c))
  rw [cast_pair_cup]
  exact has q E rfl rfl e _ _ _ _ (hp i j) (hp (i + j) l) (hp j l) (isTwPair_cast _ e (hp i (j + l)))
    rfl rfl rfl (rfl.trans hs) a b c

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleTwistedCupGradedCommOfFlipAndUniquePairing
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.cc_cup_flip : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (ν : Pair J I K), μ.IsFlip ν → ∀ (E : Spc) {n m k : ℤ}
    (h : n + m = k) (h' : m + n = k) a b, μ.cup E h a b = (n * m).negOnePow • ν.cup E h' b a

def LateralTheory.EtaleFoundations.cc_flip_ex : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K), ∃ ν : Pair J I K, μ.IsFlip ν

def LateralTheory.EtaleFoundations.cc_twpair : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j : ℤ), IsTwPair (twPair q i j) ∧ ∀ (k : ℤ), i + j = k →
    ∀ μ ν : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q k)), IsTwPair μ → IsTwPair ν →
    ∀ (E : Spc) {n m w : ℤ} (h : n + m = w), μ.cup E h = ν.cup E h

theorem LateralTheory.EtaleFoundations.cc_cup_eq_of_twPair (htw : LateralTheory.EtaleFoundations.cc_twpair) (q : ℕ) [NeZero q] (E : Spc) {n m i j : ℤ}
    (a : Ht q E n i) (b : Ht q E m j) (k : ℤ) (hk : j + i = k)
    (ν : Pair (res _ (tw q j)) (res _ (tw q i)) (res _ (tw q k))) (hν : IsTwPair ν) (w : ℤ) (hw : m + n = w) :
    ν.cup E hw b a = (cup q b a).cast hw hk := by
  subst hk hw
  obtain ⟨h1, h2⟩ := htw q j i
  have := h2 (j + i) rfl ν (twPair q j i) hν h1 E (n := m) (m := n) rfl
  rw [this]
  rfl

theorem LateralTheory.EtaleFoundations.etale_twisted_cup_graded_comm_of_flip_and_unique_pairing (hflip : LateralTheory.EtaleFoundations.cc_cup_flip) (hex : LateralTheory.EtaleFoundations.cc_flip_ex)
    (htw : LateralTheory.EtaleFoundations.cc_twpair) : LateralTheory.EtaleFoundations.EtaleTwistedCupProductGradedCommutative := by
  intro q _ E n m i j a b
  obtain ⟨ν, hν⟩ := hex (ZMod q) (twPair q i j)
  have hνtw : IsTwPair ν := by
    intro U ζ
    have := hν U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)
    rw [this, (htw q i j).1 U ζ]
    simp
  have e1 : cup q a b = (n * m).negOnePow • ν.cup E (add_comm m n) b a :=
    hflip (ZMod q) (twPair q i j) ν hν E rfl (add_comm m n) a b
  rw [e1, LateralTheory.EtaleFoundations.cc_cup_eq_of_twPair htw q E a b (i + j) (add_comm j i) ν hνtw (n + m) (add_comm m n)]
end

-- bundled from Development.EtaleCohomology.TateTwists.FirstChernSpecOfRepresentative
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def IsEtaleFirstChernKummerCocycleRep (q : ℕ) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (γ : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2) : Prop :=
  (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ.1 0 2 (by simp) U x = 0) ∧
    (∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
      ev γ.1 1 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.sub 0 1 (by omega)) →
      w ^ q = lineUnit L (x.sub 1 1 (by omega)) →
      ev γ.1 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w)

def first_chern_class_exists : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E → ∃ γ, IsEtaleFirstChernKummerCocycleRep q L γ

def first_chern_class_unique : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∀ γ γ', IsEtaleFirstChernKummerCocycleRep q L γ → IsEtaleFirstChernKummerCocycleRep q L γ' → CohomologyClass.mk γ = CohomologyClass.mk γ'

def firstChernClassTateTwist_pullback : Prop := ∀ (q : ℕ) [NeZero q] {E E' : Spc} (f : E ⟶ E') (L : E' ⟶ ofCat (glCat 1)), Inv q E' →
  ∀ γ, IsEtaleFirstChernKummerCocycleRep q L γ → ∃ γ', IsEtaleFirstChernKummerCocycleRep q (f ≫ L) γ' ∧ CohomologyClass.mk γ' = pull _ f _ _ (CohomologyClass.mk γ)

def isOneCochain_add : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L M N : E ⟶ ofCat (glCat 1)), Inv q E →
  (∀ (U : Scheme.{0}) (x : Sx E 1 U), lineUnit N x = lineUnit L x * lineUnit M x) →
  ∀ γL γM, IsEtaleFirstChernKummerCocycleRep q L γL → IsEtaleFirstChernKummerCocycleRep q M γM →
    ∃ γN, IsEtaleFirstChernKummerCocycleRep q N γN ∧ CohomologyClass.mk γN = CohomologyClass.mk γL + CohomologyClass.mk γM

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.IsTensorFlip
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex
open scoped DirectSum TensorProduct

namespace LateralTheory.EtaleFoundations.FlipPf
open GlobalTheory.EtC

variable {R : Type} [CommRing R]

lemma negOnePow_smul_smul {M : Type*} [AddCommGroup M] (n : ℤ) (x : M) :
    ((n.negOnePow : ℤ) • ((n.negOnePow : ℤ) • x)) = x := by
  rw [smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul]

lemma coef1 (s t : ℤ) : ((t * s).negOnePow : ℤ) * (t.negOnePow : ℤ) = ((t * (s + 1)).negOnePow : ℤ) := by
  rw [mul_add, mul_one, Int.negOnePow_add, Units.val_mul]

lemma coef2 (s t : ℤ) : (s.negOnePow : ℤ) * (((t + 1) * s).negOnePow : ℤ) = ((t * s).negOnePow : ℤ) := by
  rw [add_mul, one_mul, Int.negOnePow_add, Units.val_mul, mul_left_comm, ← Units.val_mul,
    Int.units_mul_self, Units.val_one, mul_one]

def flipPair {I J K : Cx R} (μ : Pair I J K) : Pair J I K where
  mul U s t w h := ((t * s).negOnePow : ℤ) • (μ.mul U t s w (by omega)).flip
  nat := by
    intro V U g s t w h b a
    simp only [LinearMap.smul_apply, LinearMap.flip_apply, map_zsmul, μ.nat]
  leibniz := by
    intro U s t w h b a
    have hl := μ.leibniz U t s w (by omega) a b
    simp only [LinearMap.smul_apply, LinearMap.flip_apply, map_zsmul]
    dsimp only [Sec.map] at hl ⊢
    rw [hl, smul_add]
    simp only [Units.smul_def, smul_smul, coef1, coef2]
    exact add_comm _ _

def swIx {w : ℤ} (p : {p : ℤ × ℤ // p.1 + p.2 = w}) : {p : ℤ × ℤ // p.1 + p.2 = w} :=
  ⟨(p.1.2, p.1.1), by have := p.2; simp only at this ⊢; omega⟩

def sw (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] Tens J I U w :=
  DirectSum.toModule _ _ _ fun p =>
    ((p.1.1 * p.1.2).negOnePow : ℤ) •
      ((DirectSum.lof (ULift.{1} R) _
        (fun q : {q : ℤ × ℤ // q.1 + q.2 = w} => Sec (J.X q.1.1) U ⊗[ULift.{1} R] Sec (I.X q.1.2) U) (swIx p)) ∘ₗ
        (TensorProduct.comm (ULift.{1} R) _ _).toLinearMap)

lemma sw_lof (I J : Cx R) (U : Scheme.{0}) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    sw I J U w (DirectSum.lof (ULift.{1} R) _
      (fun q : {q : ℤ × ℤ // q.1 + q.2 = w} => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U) p (a ⊗ₜ b)) =
    ((p.1.1 * p.1.2).negOnePow : ℤ) • DirectSum.lof (ULift.{1} R) _
      (fun q : {q : ℤ × ℤ // q.1 + q.2 = w} => Sec (J.X q.1.1) U ⊗[ULift.{1} R] Sec (I.X q.1.2) U) (swIx p) (b ⊗ₜ a) := by
  unfold sw
  erw [DirectSum.toModule_lof]
  rfl

lemma lift_lof {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    μ.lift U w (DirectSum.lof (ULift.{1} R) _
      (fun q : {q : ℤ × ℤ // q.1 + q.2 = w} => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U) p (a ⊗ₜ b)) =
    μ.mul U p.1.1 p.1.2 w p.2 a b := by
  unfold Pair.lift
  erw [DirectSum.toModule_lof]
  rfl

lemma lift_sw {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (w : ℤ) (x : Tens I J U w) :
    (flipPair μ).lift U w (sw I J U w x) = μ.lift U w x := by
  have key : (flipPair μ).lift U w ∘ₗ sw I J U w = μ.lift U w := by
    apply DirectSum.linearMap_ext; intro p; apply TensorProduct.ext'; intro a b
    simp only [LinearMap.comp_apply]
    rw [sw_lof, map_zsmul, lift_lof]
    erw [lift_lof (flipPair μ) U w (swIx p) b a]
    simp only [flipPair, LinearMap.smul_apply, LinearMap.flip_apply]
    exact negOnePow_smul_smul _ _
  exact LinearMap.congr_fun key x

lemma sw_sw (I J : Cx R) (U : Scheme.{0}) (w : ℤ) (x : Tens I J U w) :
    sw J I U w (sw I J U w x) = x := by
  have key : sw J I U w ∘ₗ sw I J U w = LinearMap.id := by
    apply DirectSum.linearMap_ext; intro p; apply TensorProduct.ext'; intro a b
    simp only [LinearMap.comp_apply, LinearMap.id_apply]
    rw [sw_lof, map_zsmul]
    erw [sw_lof J I U w (swIx p) b a]
    show ((p.1.1 * p.1.2).negOnePow : ℤ) • ((p.1.2 * p.1.1).negOnePow : ℤ) • _ = _
    rw [mul_comm p.1.2 p.1.1]
    exact negOnePow_smul_smul _ _
  exact LinearMap.congr_fun key x

lemma res_sw (I J : Cx R) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens I J U w) :
    Tens.res g w (sw I J U w x) = sw I J V w (Tens.res g w x) := by
  have key : Tens.res g w ∘ₗ sw I J U w = sw I J V w ∘ₗ Tens.res g w := by
    apply DirectSum.linearMap_ext; intro p; apply TensorProduct.ext'; intro a b
    simp only [LinearMap.comp_apply]
    rw [sw_lof, map_zsmul]
    unfold Tens.res
    erw [DirectSum.lmap_lof, DirectSum.lmap_lof, TensorProduct.map_tmul, TensorProduct.map_tmul, sw_lof]
    rfl
  exact LinearMap.congr_fun key x

lemma lift_sw' {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (w : ℤ) (x : Tens J I U w) :
    μ.lift U w (sw J I U w x) = (flipPair μ).lift U w x := by
  conv_rhs => rw [← sw_sw J I U w x]
  rw [lift_sw]

lemma isTensor_flip {I J K : Cx R} (μ : Pair I J K) (hμ : μ.IsTensor) : (flipPair μ).IsTensor := by
  obtain ⟨hs, hi⟩ := hμ
  constructor
  · intro U w y
    obtain ⟨S, hS, hP⟩ := hs U w y
    refine ⟨S, hS, fun V g hg => ?_⟩
    obtain ⟨x, hx⟩ := hP V g hg
    exact ⟨sw I J V w x, by rw [lift_sw, hx]⟩
  · intro U w x hx
    have h0 : μ.lift U w (sw J I U w x) = 0 := by rw [lift_sw', hx]
    obtain ⟨S, hS, hP⟩ := hi U w _ h0
    refine ⟨S, hS, fun V g hg => ?_⟩
    have h1 : Tens.res g w (sw J I U w x) = 0 := hP V g hg
    show Tens.res g w x = 0
    rw [← sw_sw J I U w x, res_sw, h1, map_zero]

end LateralTheory.EtaleFoundations.FlipPf

theorem LateralTheory.EtaleFoundations.etale_complex_pairing_flip_exists : LateralTheory.EtaleFoundations.EtaleComplexPairingFlipExists := by
  intro R _ I J K μ
  refine ⟨LateralTheory.EtaleFoundations.FlipPf.flipPair μ, ?_, ?_, LateralTheory.EtaleFoundations.FlipPf.isTensor_flip μ⟩
  · intro U s t w h a b
    simp only [LateralTheory.EtaleFoundations.FlipPf.flipPair, LinearMap.smul_apply, LinearMap.flip_apply, Units.smul_def]
  · intro U s t w h b a
    simp only [LateralTheory.EtaleFoundations.FlipPf.flipPair, LinearMap.smul_apply, LinearMap.flip_apply, Units.smul_def]
    rw [mul_comm s t]
    exact (LateralTheory.EtaleFoundations.FlipPf.negOnePow_smul_smul _ _).symm
end
end

-- bundled from Development.EtaleCohomology.TateTwists.SubdivisionComposition
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.SubdivisionComposition

lemma subint_comp (N j l j' l' : ℕ) (h : j + l ≤ N) (h' : j' + l' ≤ l) :
    SimplexCategory.subinterval j' l' h' ≫ SimplexCategory.subinterval j l h =
      SimplexCategory.subinterval (n := N) (j + j') l' (by omega) := by
  ext i
  change ((i : ℕ) + j' + j) = (i : ℕ) + (j + j')
  omega

lemma subint_id (N : ℕ) :
    SimplexCategory.subinterval (n := N) 0 N (by omega) = 𝟙 _ := by
  ext i
  simp [SimplexCategory.subinterval]

lemma along_comp {E : Spc} {U : Scheme.{0}} {N p r : ℕ} (x : Sx E N U)
    (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk p) :
    (x.along a).along b = x.along (b ≫ a) := by
  simp only [Sx.along, op_comp, Functor.map_comp, NatTrans.comp_app, types_comp_apply]

end LateralTheory.EtaleFoundations.SubdivisionComposition

open LateralTheory.EtaleFoundations.SubdivisionComposition in
theorem LateralTheory.EtaleFoundations.simplicial_subinterval_of_subinterval_along_etale : LateralTheory.EtaleFoundations.EtaleSimplexSubfaceComposition := by
  intro E U N x
  have hsa : ∀ (j l : ℕ) (h : j + l ≤ N), x.sub j l h = x.along (SimplexCategory.subinterval j l h) :=
    fun _ _ _ => rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j l j' l' h h'
    change (x.along _).along _ = x.along _
    rw [along_comp, subint_comp]
  · rw [hsa, subint_id]
    simp [Sx.along]
  · intro j l h
    refine ⟨?_, ?_, hsa j l h⟩
    · intro V g
      simp only [Sx.sub, Sx.res]
      have hn := ConcreteCategory.congr_hom ((E.map (SimplexCategory.subinterval j l h).op).naturality g.op) x
      simp only [ConcreteCategory.comp_apply] at hn
      exact hn
    · intro E' f
      simp only [Sx.sub, Sx.map]
      have hn := congrArg (fun t => t.app (op U)) (f.naturality (SimplexCategory.subinterval j l h).op)
      simp only [NatTrans.comp_app] at hn
      first
        | (have hm := ConcreteCategory.congr_hom hn x
           simp only [ConcreteCategory.comp_apply] at hm
           first | exact hm | exact hm.symm)
        | exact (congrFun hn x).symm
        | (rw [← types_comp_apply, ← hn]; rfl)
  · intro p r a b
    exact along_comp x a b
end

-- bundled from Development.EtaleCohomology.TateTwists.TensorLocallyBijectiveHolds
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.TensLocbij

theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

theorem loc_and {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h1 : Loc U P)
    (h2 : Loc U Q) : Loc U (fun V g => P V g ∧ Q V g) := by
  obtain ⟨S, hS, hP⟩ := h1
  obtain ⟨T, hT, hQ⟩ := h2
  exact ⟨S ⊓ T, (Scheme.etaleTopology).intersection_covering hS hT,
    fun V g hg => ⟨hP V g hg.1, hQ V g hg.2⟩⟩

theorem map_comp_apply' (R : Type) [CommRing R] (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R))
    {U V W : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (p : P.obj (op U)) :
    (P.map (k ≫ g).op).hom p = (P.map k.op).hom ((P.map g.op).hom p) := by
  simp [op_comp, Functor.map_comp]

end LateralTheory.EtaleFoundations.TensLocbij
end


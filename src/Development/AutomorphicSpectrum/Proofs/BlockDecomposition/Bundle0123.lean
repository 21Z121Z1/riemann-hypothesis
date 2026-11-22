import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0049
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0117
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClosedEmbeddingTopEmb
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0061
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0048
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0119
import Formalism.RealPlaceAnalysis.Bundle0004

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EdgeUnique
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EtSpecProof

section Sections

variable {R : Type} [CommRing R]

theorem res_comp {G : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (x : Sec G U) :
    Sec.res (k ≫ g) x = Sec.res k (Sec.res g x) := by
  simp [Sec.res]

theorem map_res {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  have h := φ.hom.naturality g.op
  exact congrArg (fun m => m.hom x) h

end Sections

variable {q : ℕ} {C : Type 1} [Category.{0} C] {P : Probe C q} {X : Scheme.{0}}

theorem map_glob (Y : P.Pts X) (i : ℤ) (j : ℕ) (a : Sec ((GlobalTheory.EtC.res _ (tw q i)).X (j : ℤ)) X)
    {c c' : C} (φ : c ⟶ c') :
    (((P.res i).K j).map φ).hom (Sec.res (Y.y c) a) = Sec.res (Y.y c') a := by
  change Sec.res (P.S.map φ).unop (Sec.res (Y.y c) a) = _
  rw [← res_comp, Y.nat]

theorem d_glob (Y : P.Pts X) (i : ℤ) (j : ℕ) (a : Sec ((GlobalTheory.EtC.res _ (tw q i)).X (j : ℤ)) X) :
    d ((P.res i).K j) 0 (Y.glob i j a) = 0 := by
  funext s
  have h : ∀ k : Fin 2, (((P.res i).K j).map (GlobalTheory.CatH.toLast k s)).hom (Y.glob i j a (GlobalTheory.CatH.face k s)) =
      Sec.res (Y.y (s.obj (Fin.last 1))) a := fun k => map_glob Y i j a _
  change ∑ k : Fin 2, (-1 : ℤ) ^ (k : ℕ) •
    (((P.res i).K j).map (GlobalTheory.CatH.toLast k s)).hom (Y.glob i j a (GlobalTheory.CatH.face k s)) = 0
  rw [Fin.sum_univ_two, h 0, h 1]
  simp

theorem dvC_glob (Y : P.Pts X) (i : ℤ) (j : ℕ) (a : Sec ((GlobalTheory.EtC.res _ (tw q i)).X (j : ℤ)) X) :
    (P.res i).dvC j 0 (Y.glob i j a) =
      Y.glob i (j + 1) (Sec.map ((GlobalTheory.EtC.res _ (tw q i)).d (j : ℤ) ((j + 1 : ℕ) : ℤ)) a) := by
  funext s
  exact map_res _ _ _

theorem glob_add (Y : P.Pts X) (i : ℤ) (j : ℕ) (a b : Sec ((GlobalTheory.EtC.res _ (tw q i)).X (j : ℤ)) X) :
    Y.glob i j (a + b) = Y.glob i j a + Y.glob i j b := by
  funext s
  exact map_add _ _ _

theorem glob_sub (Y : P.Pts X) (i : ℤ) (j : ℕ) (a b : Sec ((GlobalTheory.EtC.res _ (tw q i)).X (j : ℤ)) X) :
    Y.glob i j (a - b) = Y.glob i j a - Y.glob i j b := by
  funext s
  exact map_sub _ _ _

theorem edge_exists {i : ℤ} {j : ℕ} (hT : (P.res i).Good) (hSE : StEx) (hRB : RepBasic) (Y : P.Pts X)
    {x : Ht q (sch.obj X) j i} {a : Sec ((GlobalTheory.EtC.res _ (tw q i)).X (j : ℤ)) X} (hx : Rep x a) :
    ∃ h, (P.res i).Edge (Y.glob i j a) h := by
  have hcl := (hRB (ZMod q) (GlobalTheory.EtC.res _ (tw q i)) X (j : ℤ)).2.1 x a hx ((j + 1 : ℕ) : ℤ)
  have hdv : (P.res i).dvC j 0 (Y.glob i j a) = 0 := by
    rw [dvC_glob, hcl]
    funext s
    exact map_zero _
  obtain ⟨z, hz, hst⟩ := hSE ℤ C P.L (P.res i) hT j 0 j (add_zero j) (Y.glob i j a) hdv (d_glob Y i j a)
  exact ⟨(cx P.L).cls z hz, z, hz, hst, rfl⟩

theorem edge_unique {i : ℤ} {j : ℕ} (hT : (P.res i).Good) (hEU : EdgeUniq) (hRB : RepBasic) (hRZ : ResZero)
    (Y : P.Pts X) {x : Ht q (sch.obj X) j i} {a a' : Sec ((GlobalTheory.EtC.res _ (tw q i)).X (j : ℤ)) X}
    (hx : Rep x a) (hx' : Rep x a') {h h' : H P.L j} (he : (P.res i).Edge (Y.glob i j a) h)
    (he' : (P.res i).Edge (Y.glob i j a') h') : h = h' := by
  have hB := hRB (ZMod q) (GlobalTheory.EtC.res _ (tw q i)) X (j : ℤ)
  have h0 : Rep (0 : Ht q (sch.obj X) j i) (a - a') := by
    have := (hB.2.2.1 x x a a' hx hx').2
    rwa [sub_self] at this
  have hz := hB.2.2.2.1 (a - a') h0
  have hVB : (P.res i).VB j (Y.glob i j a - Y.glob i j a') := by
    cases j with
    | zero =>
      obtain ⟨b, hb⟩ := hz (-1) (by norm_num)
      have := (hRZ (ZMod q) (tw q i) X).2.2 (-1) (by norm_num)
      have hb0 : b = 0 := Subsingleton.elim _ _
      have hz0 : a - a' = 0 := by
        rw [← hb, hb0]
        exact map_zero _
      change Y.glob i 0 a - Y.glob i 0 a' = 0
      rw [← glob_sub, hz0]
      funext s
      exact map_zero _
    | succ s =>
      obtain ⟨b, hb⟩ := hz (s : ℤ) (by push_cast; rfl)
      refine ⟨Y.glob i s b, d_glob Y i s b, ?_⟩
      rw [dvC_glob, hb, glob_sub]
  exact (hEU ℤ C P.L (P.res i) hT j _ _ h h' he he').2 hVB

theorem etSpec : ResGood → StEx → EdgeUniq → RepBasic → ResZero → EtSpec := by
  intro hRG hSE hEU hRB hRZ hGen q _ C _ P X Y i j x
  have hT := hRG hGen q C P i
  have hB := hRB (ZMod q) (GlobalTheory.EtC.res _ (tw q i)) X (j : ℤ)
  have hex : ∀ x, ∃ h, Y.IsEt i j x h := fun x => by
    obtain ⟨a, ha⟩ := hB.1 x
    obtain ⟨h, hh⟩ := edge_exists hT hSE hRB Y ha
    exact ⟨h, a, ha, hh⟩
  have huniq : ∀ {x h h'}, Y.IsEt i j x h → Y.IsEt i j x h' → h = h' := by
    rintro x h h' ⟨a, ha, he⟩ ⟨a', ha', he'⟩
    exact edge_unique hT hEU hRB hRZ Y ha ha' he he'
  have hall : ∀ x, Y.IsEt i j x (Y.et i j x) := by
    refine pick_spec (P := fun e : Ht q (sch.obj X) j i →+ H P.L j => ∀ x, Y.IsEt i j x (e x)) ?_
    choose f hf using hex
    refine ⟨AddMonoidHom.mk' f fun u v => huniq (hf _) ?_, hf⟩
    obtain ⟨a, ha, he⟩ := hf u
    obtain ⟨b, hb, he'⟩ := hf v
    refine ⟨a + b, (hB.2.2.1 u v a b ha hb).1, ?_⟩
    rw [glob_add]
    exact (hEU ℤ C P.L (P.res i) hT j _ _ _ _ he he').1
  refine ⟨fun a ha => ?_, fun h hh => huniq hh (hall x)⟩
  obtain ⟨h, hh⟩ := edge_exists hT hSE hRB Y ha
  have e : h = Y.et i j x := huniq ⟨a, ha, hh⟩ (hall x)
  rwa [← e]

end GlobalTheory.CompanionTheory.EtSpecProof
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EtaleChernClassEqKummerClass
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EtaleChernClass

open GlobalTheory.CatH (face toLast)

universe w

section Cochains

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{w} R)

theorem d_zero_apply (f : Cn F 0) (s : ComposableArrows C 1) :
    d F 0 f s = (show F.obj (s.obj (Fin.last 1)) from f (face 0 s)) - (show F.obj (s.obj (Fin.last 1)) from (F.map (s.map' 0 1)).hom (f (face 1 s))) := by
  change ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (F.map (toLast i s)).hom (f (face i s)) = _
  rw [Fin.sum_univ_two]
  have e0 : toLast (0 : Fin 2) s = 𝟙 _ := s.map_id _
  have e1 : toLast (1 : Fin 2) s = s.map' 0 1 := rfl
  rw [e0, e1, F.map_id]
  simp [sub_eq_add_neg]
  rfl

theorem d_one_apply (f : Cn F 1) (s : ComposableArrows C 2) :
    d F 1 f s = (show F.obj (s.obj (Fin.last 2)) from f (face 0 s)) - (show F.obj (s.obj (Fin.last 2)) from f (face 1 s)) +
      (show F.obj (s.obj (Fin.last 2)) from (F.map (s.map' 1 2)).hom (f (face 2 s))) := by
  change ∑ i : Fin 3, (-1 : ℤ) ^ (i : ℕ) • (F.map (toLast i s)).hom (f (face i s)) = _
  rw [Fin.sum_univ_three]
  have e0 : toLast (0 : Fin 3) s = 𝟙 _ := s.map_id _
  have e1 : toLast (1 : Fin 3) s = 𝟙 _ := s.map_id _
  have e2 : toLast (2 : Fin 3) s = s.map' 1 2 := rfl
  rw [e0, e1, e2, F.map_id]
  simp [sub_eq_add_neg]
  rfl

end Cochains

theorem close_sum {M : Type*} [AddCommGroup M] (tce tbe tbc kv kw ku kvw i : M)
    (h₁ : tce - tbe + tbc = kv + kw - kvw) (h₂ : kvw = ku + i) :
    (-1 : ℤ) ^ 1 • ((tce - kw) - (tbe - ku) + (tbc - kv)) = i := by
  have e : tce = kv + kw - kvw + tbe - tbc := by rw [← h₁]; abel
  rw [e, h₂]
  simp only [pow_one, neg_smul, one_smul]
  abel

theorem u_congr {X : Scheme.{0}} (D : LineData X) {V : Scheme.{0}} {a a' b b' : V ⟶ D.Y}
    (h : a ≫ D.f = b ≫ D.f) (h' : a' ≫ D.f = b' ≫ D.f) (ha : a = a') (hb : b = b') :
    D.u a b h = D.u a' b' h' := by
  subst ha hb; rfl

theorem etale_chern_class_eq_kummer_class : CrystallineSemistableComparison.E.EtSpec → CrystallineSemistableComparison.E.ResGood → CrystallineSemistableComparison.E.StCol → CrystallineSemistableComparison.E.FirstChernCoboundary → CrystallineSemistableComparison.E.KumPow →
    CrystallineSemistableComparison.E.EtaleFirstChernKummer := by
  intro hES hRG hSC hCP hKP hGen hKum hC1 q _ C _ P X Y D L hL hInv x hx z Λ
  obtain ⟨a, η, θ, hRep, hηn, hθn, hdη, hdiff, hcoc⟩ := hCP hC1 q X D L hL hInv x hx
  have hθc : ∀ (V : Scheme.{0}) (b b' c : V ⟶ D.Y) (h : b ≫ D.f = c ≫ D.f) (h' : b' ≫ D.f = c ≫ D.f),
      b = b' → θ V b c h = θ V b' c h' := by
    intro V b b' c h h' e
    subst e
    rfl
  have hG : (P.res 1).Good := hRG hGen q C P 1
  obtain ⟨hιd, hdd, hinj, -, -⟩ := hSC ℤ C P.L (P.res 1) hG
  have hpp : ∀ {c c' : C} (φ : c ⟶ c'), ((P.S.map φ).unop ≫ Λ.p c) ≫ D.f = Λ.p c' ≫ D.f := by
    intro c c' φ
    rw [Category.assoc, Λ.hp, Λ.hp, Y.nat]
  let A₀ : ∀ {c c' : C} (φ : c ⟶ c'), Sec ((res _ (tw q 1)).X 0) (P.U c') := fun {c c'} φ =>
    θ _ ((P.S.map φ).unop ≫ Λ.p c) (Λ.p c') (hpp φ) - kumT q _ (Λ.r φ)
  let a₁ : Cn ((P.res 1).K 1) 0 := fun s => η _ (Λ.p (s.obj 0))
  let a₀ : Cn ((P.res 1).K 0) 1 := fun s => A₀ (s.map' 0 1)
  have h1 : (P.res 1).dvC 1 0 a₁ = Y.glob 1 2 a := by
    funext s
    refine (hdη _ (Λ.p (s.obj 0))).trans ?_
    rw [Λ.hp]
    rfl
  have h2 : (-1 : ℤ) ^ 0 • d ((P.res 1).K 1) 0 a₁ = (P.res 1).dvC 0 1 a₀ := by
    funext s
    rw [pow_zero, one_smul, d_zero_apply]
    have e := hdiff _ ((P.S.map (s.map' 0 1)).unop ≫ Λ.p (s.obj 0)) (Λ.p (s.obj 1)) (hpp (s.map' 0 1)) _ (Λ.hr _)
    rw [← hηn] at e
    exact e
  have h3 : (-1 : ℤ) ^ 1 • d ((P.res 1).K 0) 1 a₀ = (P.res 1).ιC 2 z := by
    funext s
    rw [Pi.smul_apply, d_one_apply]
    let g := (P.S.map (s.map' 1 2)).unop
    have hg : g ≫ (P.S.map (s.map' 0 1)).unop = (P.S.map (s.map' 0 2)).unop := by
      have e : s.map' 0 2 = s.map' 0 1 ≫ s.map' 1 2 := s.map_comp _ _
      rw [e, P.S.map_comp, unop_comp]
    have hb : g ≫ (P.S.map (s.map' 0 1)).unop ≫ Λ.p (s.obj 0) =
        (P.S.map (s.map' 0 2)).unop ≫ Λ.p (s.obj 0) := by
      rw [← Category.assoc, hg]
    have hbc' : (g ≫ (P.S.map (s.map' 0 1)).unop ≫ Λ.p (s.obj 0)) ≫ D.f = (g ≫ Λ.p (s.obj 1)) ≫ D.f := by
      have e : ((P.S.map (s.map' 0 1)).unop ≫ Λ.p (s.obj 0)) ≫ D.f = Λ.p (s.obj 1) ≫ D.f := hpp (s.map' 0 1)
      rw [Category.assoc g, e, Category.assoc]
    have hbc : ((P.S.map (s.map' 0 2)).unop ≫ Λ.p (s.obj 0)) ≫ D.f = (g ≫ Λ.p (s.obj 1)) ≫ D.f := by
      rw [← hb]
      exact hbc'
    let v := Units.map g.appTop.hom.toMonoidHom (Λ.r (s.map' 0 1))
    let w := Λ.r (s.map' 1 2)
    let u := Λ.r (s.map' 0 2)
    have hv : v ^ q = D.u _ _ hbc := by
      change Units.map g.appTop.hom.toMonoidHom (Λ.r (s.map' 0 1)) ^ q = _
      rw [← map_pow, Λ.hr, ← D.nat]
      exact u_congr D _ _ hb rfl
    have hw : w ^ q = D.u (g ≫ Λ.p (s.obj 1)) (Λ.p (s.obj 2)) (hpp (s.map' 1 2)) := Λ.hr _
    have hc := hcoc _ _ _ _ hbc (hpp (s.map' 1 2)) v w hv hw
    have hk := hKP hKum q _ (P.ζ (s.obj (Fin.last 2))) (z s) (v * w * u⁻¹) u (Λ.hz s)
    rw [inv_mul_cancel_right] at hk
    have hn : ((((P.res 1).K 0).map (s.map' 1 2)).hom (a₀ (face 2 s))) =
        θ _ ((P.S.map (s.map' 0 2)).unop ≫ Λ.p (s.obj 0)) (g ≫ Λ.p (s.obj 1)) hbc - kumT q _ v := by
      have t₁ : Sec.res g (θ _ ((P.S.map (s.map' 0 1)).unop ≫ Λ.p (s.obj 0)) (Λ.p (s.obj 1)) (hpp (s.map' 0 1))) =
          θ _ ((P.S.map (s.map' 0 2)).unop ≫ Λ.p (s.obj 0)) (g ≫ Λ.p (s.obj 1)) hbc :=
        (hθn _ _ g _ _ _ hbc').trans (hθc _ _ _ _ _ _ hb)
      have t₂ : Sec.res g (kumT q _ (Λ.r (s.map' 0 1))) = kumT q _ v := (hKum q).1 _ _ g _ (P.ζ _).2.1
      exact (map_sub _ _ _).trans (congrArg₂ (· - ·) t₁ t₂)
    rw [hn]
    exact close_sum _ _ _ _ _ _ _ _ hc hk
  have hSt : (P.res 1).St z 2 0 (Y.glob 1 2 a) := ⟨a₁, h1, a₀, h2.symm, rfl, h3.symm⟩
  have hz : d P.L 2 z = 0 := by
    apply hinj 3
    rw [map_zero, ← hιd, ← h3, map_smul, d_d, smul_zero]
  exact ⟨hz, ((hES hGen q C P X Y 1 2 x).2 _ ⟨a, hRep, z, hz, hSt, rfl⟩).symm⟩

end GlobalTheory.CompanionTheory.EtaleChernClass
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHermitianCongrToOne
section
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

namespace GlobalTheory.CompanionTheory.UnrDens

theorem exists_congr_one : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε →
    ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E), cT τ T = T → IsUnit T.det →
      ∃ g : Matrix (Fin n) (Fin n) E, IsUnit g.det ∧ cT τ g * T * g = 1 := by
  intro E _ τ q ε hR n T hT hdet
  have hinv : ∀ a : E, τ (τ a) = a := hR.inv
  have hq : 1 < q := hR.one_lt
  have hcard : Nat.card (Fin n → E) = q ^ (2 * n) := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin, hR.card, ← pow_mul]
  have hcnt := GlobalTheory.T.card_orthonormal_frames_hermitian_space E τ q ε hR n n le_rfl (Fin n → E) (HermSp.ofMatrix hinv T hT hdet) hcard
  have hε : ε = -1 ∨ ε = 1 := by
    rcases hR.eps with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hne : Nat.card {x : Fin n → Fin n → E // ∀ i j : Fin n,
      (HermSp.ofMatrix hinv T hT hdet).h (x i) (x j) = if i = j then 1 else 0} ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero, eq_comm, Finset.prod_eq_zero_iff] at hcnt
    obtain ⟨i, -, hi⟩ := hcnt
    have hk : n - (i : ℕ) ≠ 0 := Nat.sub_ne_zero_of_lt i.isLt
    rcases mul_eq_zero.mp hi with h | h
    · rw [div_eq_zero_iff] at h
      rcases h with h | h
      · have h' := pow_eq_zero_iff (n := 2 * (n - (i : ℕ))) (by omega) |>.mp h
        rw [Nat.cast_eq_zero] at h'
        omega
      · rw [Nat.cast_eq_zero] at h
        omega
    · rw [sub_eq_zero] at h
      have h2 := congrArg abs h
      rw [abs_one, abs_pow, abs_div, Nat.abs_cast] at h2
      have key : ∀ {F : Type} [Field F] [LinearOrder F] [IsStrictOrderedRing F] (e : ℤ) (k : ℕ),
          (e = -1 ∨ e = 1) → k ≠ 0 → (1 : F) ≠ (|(e : F)| / (q : F)) ^ k := by
        intro F _ _ _ e k he hk' hh
        have hqF : (1 : F) < q := by exact_mod_cast hq
        have habs : |(e : F)| = 1 := by
          rcases he with rfl | rfl <;> simp
        rw [habs] at hh
        have hlt : (1 / (q : F)) ^ k < 1 :=
          pow_lt_one₀ (by positivity) ((div_lt_one (by linarith)).mpr hqF) hk'
        linarith
      exact key ε _ hε hk h2
  obtain ⟨⟨x, hx⟩⟩ := (Nat.card_ne_zero.mp hne).1
  have hg : cT τ (Matrix.of fun a i => x i a) * T * (Matrix.of fun a i => x i a) = 1 := by
    ext i j
    rw [gram_apply hinv T hT hdet]
    show (HermSp.ofMatrix hinv T hT hdet).h (x j) (x i) = (1 : Matrix (Fin n) (Fin n) E) i j
    rw [hx j i, Matrix.one_apply]
    by_cases h : i = j
    · subst h
      simp
    · rw [if_neg (Ne.symm h), if_neg h]
  exact ⟨_, Matrix.isUnit_det_of_left_inverse hg, hg⟩

end GlobalTheory.CompanionTheory.UnrDens
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibRepApply
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof Matrix Topology

namespace GlobalTheory.CompanionTheory.ThetaGLLen

section Abstract

variable {Γ G V : Type} [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V]

def twRel (ρ : Representation ℂ Γ V) (ψ : Γ →* ℂˣ) : Submodule ℂ V :=
  Submodule.span ℂ {w | ∃ (γ : Γ) (v : V), w = ρ γ v - (ψ γ : ℂ) • v}

theorem twRel_stable (τ : Representation ℂ (Γ × G) V) (ψ : Γ →* ℂˣ) (g : G) (v : V)
    (hv : v ∈ twRel (τ.comp (MonoidHom.inl Γ G)) ψ) :
    τ (1, g) v ∈ twRel (τ.comp (MonoidHom.inl Γ G)) ψ := by
  have h : twRel (τ.comp (MonoidHom.inl Γ G)) ψ ≤
      (twRel (τ.comp (MonoidHom.inl Γ G)) ψ).comap (τ (1, g)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨γ, u, rfl⟩
    refine Submodule.subset_span ⟨γ, τ (1, g) u, ?_⟩
    have e : τ (1, g) (τ (γ, 1) u) = τ (γ, 1) (τ (1, g) u) := by
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
      simp
    simp [e]
  exact h hv

def coinv (τ : Representation ℂ (Γ × G) V) (ψ : Γ →* ℂˣ) :
    Representation ℂ G (V ⧸ twRel (τ.comp (MonoidHom.inl Γ G)) ψ) :=
  Representation.quotient (τ.comp (MonoidHom.inr Γ G) : Representation ℂ G V) _
    (fun g v hv => twRel_stable τ ψ g v hv)

end Abstract

section Fibre

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (a c d : Type) [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]

def fibChar (μ : kˣ →* ℂˣ) : GL a k × (GL c k × GL d k) →* ℂˣ :=
  (detChar a (μ⁻¹ * absPow k (((Fintype.card c : ℂ) + Fintype.card d) / 2))).comp (MonoidHom.fst _ _) *
    (detChar c (μ * absPow k (-(Fintype.card a : ℂ) / 2) * absPow k (-(Fintype.card d : ℂ) / 2))).comp
      ((MonoidHom.fst _ _).comp (MonoidHom.snd _ _)) *
    (detChar d (μ * absPow k (-(Fintype.card a : ℂ) / 2) * absPow k ((Fintype.card c : ℂ) / 2))).comp
      ((MonoidHom.snd _ _).comp (MonoidHom.snd _ _))

def fibBase (κ : ℕ) : Representation ℂ (GL a k × GL c k) (SB (RankIn k a c {κ})) :=
  sbRep (fun x γ => ⟨act x.1 γ, by rw [rank_act]; exact x.2⟩)
    (fun x => Subtype.ext (act_one x.1)) (fun x γ δ => Subtype.ext (act_mul x.1 γ δ))
    (fun γ => ((continuous_act γ).comp continuous_subtype_val).subtype_mk _)

def fibRep (μ : kˣ →* ℂˣ) (κ : ℕ) :
    Representation ℂ (GL a k × (GL c k × GL d k)) (SB (RankIn k a c {κ})) :=
  twist ((fibBase a c κ).comp ((MonoidHom.id _).prodMap (MonoidHom.fst _ _))) (fibChar a c d μ)

theorem fibRep_apply (μ : kˣ →* ℂˣ) (κ : ℕ) (g : GL a k) (p₁ : GL c k) (p₂ : GL d k)
    (φ : SB (RankIn k a c {κ})) (y : RankIn k a c {κ}) :
    (fibRep a c d μ κ (g, p₁, p₂) φ).1 y = (fibChar a c d μ (g, p₁, p₂) : ℂ) *
      φ.1 ⟨act y.1 (g, p₁), by rw [rank_act]; exact y.2⟩ := rfl

def rightRep (κ : ℕ) : Representation ℂ (GL a k) (SB (RankIn k a c {κ})) :=
  (fibBase a c κ).comp (MonoidHom.inl _ _)

end Fibre

end GlobalTheory.CompanionTheory.ThetaGLLen
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsKumPow
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.KumPowProof

theorem isKum_pow {q : ℕ} {t : ∀ U : Scheme.{0}, (Γ(U, ⊤))ˣ → Sec ((res _ (tw q 1)).X 0) U} (ht : IsKum q t)
    {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) (v : (Γ(U, ⊤))ˣ) (k : ℕ) :
    ∀ w : (Γ(U, ⊤))ˣ, (w : Γ(U, ⊤)) = ζ.1 ^ k * v → t U w = t U v + k • resGen 1 ζ := by
  induction k with
  | zero =>
    intro w hw
    rw [pow_zero, one_mul] at hw
    rw [Units.ext hw, zero_smul, add_zero]
  | succ k ih =>
    intro w hw
    have hw' : (w : Γ(U, ⊤)) = ζ.1 * (ζ.1 ^ k * v) := by rw [hw]; ring
    obtain ⟨z, hz⟩ : IsUnit (ζ.1 ^ k * v) := isUnit_of_mul_isUnit_right (hw' ▸ w.isUnit)
    rw [ht.2 U ζ z w (by rw [hw', hz]), ih z hz, succ_nsmul, add_assoc]

theorem res_smap {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  have h := φ.hom.naturality g.op
  exact (congrArg (fun m => m.hom x) h).symm

theorem kumPow : LcCover → RepRoot → KapSpec → PrimAlg → KumPow := by
  intro hL _ hK _ hKum q _ U ζ f r v hr
  have ht : IsKum q (kumT q) := hKum q
  have hq : IsUnit (q : Γ(U, ⊤)) := ζ.2.1
  obtain ⟨W, j, hf, -, -, hG⟩ := hL U (ZMod q) f
  obtain ⟨y, -, huniq⟩ := hG (ZMod q) ((res _ (tw q 1)).X 0) (fun a => Sec.res (j a) (kumT q U (r * v)))
  refine (huniq _ fun a => rfl).trans (huniq _ fun a => ?_).symm
  have hra : (j a).appTop.hom r.val = (primRes (j a) ζ).1 ^ a.val := hr (W a) (j a) a (hf a)
  have hlc : Sec.res (j a) (kap 1 ζ f) = (ULift.up a : ULift.{1} (ZMod q)) • twGen 1 (primRes (j a) ζ) :=
    (hK q 1 U ζ f).1 (W a) (j a) a (hf a)
  have hup : (ULift.up a : ULift.{1} (ZMod q)) = a.val • (1 : ULift.{1} (ZMod q)) :=
    ULift.ext _ _ (by change a = a.val • (1 : ZMod q); simp)
  have hsm : Sec.res (j a) (kap 1 ζ f) = a.val • twGen 1 (primRes (j a) ζ) := by
    rw [hlc, hup, smul_assoc, one_smul]
  have hkey := isKum_pow ht (primRes (j a) ζ) (Units.map (j a).appTop.hom.toMonoidHom v) a.val
    (Units.map (j a).appTop.hom.toMonoidHom (r * v)) (by
      change (j a).appTop.hom (r.val * v.val) = _ * (j a).appTop.hom v.val
      rw [map_mul, hra])
  have e1 : Sec.res (j a) (kumT q U (r * v)) = kumT q (W a) (Units.map (j a).appTop.hom.toMonoidHom (r * v)) :=
    ht.1 _ _ (j a) _ hq
  have e2 : Sec.res (j a) (kumT q U v) = kumT q (W a) (Units.map (j a).appTop.hom.toMonoidHom v) :=
    ht.1 _ _ (j a) _ hq
  have e3 : Sec.res (j a) (Sec.map (resι _ (tw q 1)) (kap 1 ζ f)) = a.val • resGen 1 (primRes (j a) ζ) := by
    rw [res_smap, hsm]
    exact map_nsmul _ _ _
  have e0 : Sec.res (j a) (kumT q U v + Sec.map (resι _ (tw q 1)) (kap 1 ζ f)) =
      Sec.res (j a) (kumT q U v) + Sec.res (j a) (Sec.map (resι _ (tw q 1)) (kap 1 ζ f)) := map_add _ _ _
  rw [e0, e1, e2, e3, hkey]

end GlobalTheory.CompanionTheory.KumPowProof
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KapOneEqTwGen
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeRoot

theorem kap_one_eq_twGen (hRep : CrystallineSemistableComparison.E.RepRoot) (hKap : CrystallineSemistableComparison.E.KapSpec) {q : ℕ} (i : ℤ) {U : Scheme.{0}}
    (ζ : Prim q Γ(U, ⊤)) : kap i ζ 1 = twGen i ζ := by
  refine ((hKap q i U ζ 1).2.1 (twGen i ζ) ?_).symm
  intro V g a h
  rw [((hRep q i U ζ).1 V g).1]
  by_cases hV : Nonempty V
  · obtain ⟨v⟩ := hV
    have ha : (1 : ZMod q) = a := h v
    subst ha
    exact (one_smul _ _).symm
  · have hV' : IsEmpty V := not_nonempty_iff.1 hV
    have h0 := (hKap q i U ζ 1).1 V g 0 (fun v => hV'.elim v)
    have h1 := (hKap q i U ζ 1).1 V g 1 (fun v => hV'.elim v)
    have hz : twGen i (primRes g ζ) = 0 := by
      have e : (ULift.up (1 : ZMod q) : ULift.{1} (ZMod q)) • twGen i (primRes g ζ) =
          (ULift.up (0 : ZMod q) : ULift.{1} (ZMod q)) • twGen i (primRes g ζ) := h1.symm.trans h0
      have e1 : (ULift.up (1 : ZMod q) : ULift.{1} (ZMod q)) • twGen i (primRes g ζ) = twGen i (primRes g ζ) :=
        one_smul _ _
      have e0 : (ULift.up (0 : ZMod q) : ULift.{1} (ZMod q)) • twGen i (primRes g ζ) = 0 := zero_smul _ _
      rw [e1, e0] at e
      exact e
    rw [hz, smul_zero]

theorem d_one_eq_zero {C : Type 1} [Category.{0} C] {R : Type} [CommRing R] (A : C ⥤ CommAlgCat.{0} R) :
    d (modF A) 0 (fun s => (1 : A.obj (s.obj (Fin.last 0)))) = 0 := by
  funext s
  change ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (A.map (GlobalTheory.CatH.toLast i s)).hom 1 = (0 : A.obj _)
  rw [Fin.sum_univ_two, map_one, map_one]
  simp

theorem etRoot_of_spec : CrystallineSemistableComparison.E.EtSpec → CrystallineSemistableComparison.E.RepRoot → CrystallineSemistableComparison.E.KapSpec → CrystallineSemistableComparison.E.EtRoot := by
  intro hEt hRep hKap hGen q _ C _ P X Y ζ hζ i
  refine ((hEt hGen q C P X Y i 0 (rootClass i ζ)).2 _ ?_).symm
  refine ⟨resGen i ζ, (hRep q i X ζ).2, ?_⟩
  refine ⟨fun s => (1 : (lcF P.S q).obj (s.obj (Fin.last 0))), d_one_eq_zero (lcF P.S q), ?_, rfl⟩
  refine ⟨rfl, ?_⟩
  funext s
  change Sec.map (resι _ (tw q i)) (kap i (P.ζ (s.obj (Fin.last 0))) 1) = Sec.res (Y.y (s.obj (Fin.last 0))) (resGen i ζ)
  rw [kap_one_eq_twGen hRep hKap, ((hRep q i X ζ).1 _ _).2, hζ]
  rfl

end GlobalTheory.CompanionTheory.EdgeRoot
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuantumDetAdjointFormStatement
section
open Formalism.REAL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quantum_det_adjoint_form : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (n : ℕ) (X Y : Fin n → Fin n → Module.End ℂ V), Formalism.REAL.GlRel Y → (∀ (i j : Fin n) (φ ψ : V), B (X i j φ) ψ = -B φ (Y i j ψ)) → ∀ (v : ℂ) (φ ψ : V), B (Formalism.REAL.qdet X v φ) ψ = B φ ((((-1 : ℂ) ^ n) • Formalism.REAL.qdet Y ((n : ℂ) - 1 - (starRingEnd ℂ) v)) ψ) := by
  first | exact @GlobalTheory.CompanionTheory.CapelliAdj.adj_qdet | exact GlobalTheory.CompanionTheory.CapelliAdj.adj_qdet | (intros; apply GlobalTheory.CompanionTheory.CapelliAdj.adj_qdet <;> assumption)
end


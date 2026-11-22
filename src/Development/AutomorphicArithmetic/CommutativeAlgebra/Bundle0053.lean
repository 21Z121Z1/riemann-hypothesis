import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3204
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1660
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0136
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0045

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.HeckeLiftExistsOfQuotientLevel
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.crystallineComparison.Mod (Std TjD TjE KSOKE)
open UpperTheory.Gal.Int.Geo
open scoped TensorProduct

section SlopeTestRemainingChoices

variable {q : ℕ} [Fact q.Prime] {D : Datum q} {R R' : Type} [CommRing R] [CommRing R'] [Algebra ℚ R'] {b : Base D R}
  {gb : GBase D.toG R'} {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R'} {N N₀ c : ℕ}

private theorem qcast {o' : GObj gb N s'} {o : Obj b N₀ s} {f g : S' ⟶ S} (e : f = g) (n : QMap o' o f c) :
    ∃ n' : QMap o' o g c, n'.φ = n.φ := by
  subst e
  exact ⟨n, rfl⟩

private theorem qobj' (hObj : QObj) (β : R →+* R') (hm : Match b gb β) (hN : N = N₀ * c) (h0 : 0 < N) (hc : N₀.Coprime q)
    (o : GObj gb N s') {s₀ : S' ⟶ Sp R} (e : s₀ = s' ≫ spMap β) : ∃ o₀ : Obj b N₀ s₀, Nonempty (QMap o o₀ (𝟙 S') c) := by
  subst e
  exact hObj q D R R' b gb β hm N N₀ c hN h0 hc S' s' o

private theorem sec_hom {X : Scheme.{0}} {A : Over X} (e : 𝟙_ (Over X) ⟶ A) : e.left ≫ A.hom = 𝟙 X := by
  simpa using Over.w e

private theorem sec_lift {X Y : Scheme.{0}} {A : Over X} {B : Over Y} {f : X ⟶ Y} {φ : A.left ⟶ B.left}
    (hc : IsPullback φ A.hom B.hom f) (e : 𝟙_ (Over Y) ⟶ B) : ∃ l : 𝟙_ (Over X) ⟶ A, l.left ≫ φ = f ≫ e.left := by
  refine ⟨Over.homMk (hc.lift (f ≫ e.left) (𝟙 X) (by simp [sec_hom e])) (by simp), ?_⟩
  simp

end SlopeTestRemainingChoices

theorem UpperTheory.hecke_lift_exists_of_quotient_level :
    NumEx → QObj → QComp → QUniq → QLev → TjIsog → TrEta → CongCRT → LiftEx := by
  intro hNumEx hQObj hQComp hQUniq hQLev hTjIsog hTrEta hCRT p _ D G L E _ _ gb w q _ r 𝔴 𝔫 S k T K₀ hLev i h hi hTj hInt Tj Lj N' N t c a hN't hNum C' C u hu W
  obtain ⟨hNc, hGen⟩ := hNum
  have hN'c : (N' : ℕ) = S.N₀ * (c * t) := by rw [hN't, hNc, _root_.mul_assoc]
  have h3 : 3 ≤ S.N₀ := S.std.three
  have hcq : S.N₀.Coprime q := S.std.cop
  have hNpos : 0 < (N : ℕ) := by have := N.2.1; omega
  have hN'pos : 0 < (N' : ℕ) := by have := N'.2.1; omega
  have e0 : (C'.j ≫ S.π) ≫ S.M.s = (T.M N').s ≫ spMap (algebraMap (Ow w) E) := by
    rw [Category.assoc, S.ov, C'.ov]
  obtain ⟨o₁, ⟨n₁⟩⟩ := qobj' hQObj (algebraMap (Ow w) E) S.mat hN'c hN'pos hcq (T.M N').univ e0
  obtain ⟨o₂, ⟨n₂⟩⟩ := qobj' hQObj (algebraMap (Ow w) E) S.mat hNc hNpos hcq W.o e0
  obtain ⟨ψ₀, hψ₀, hiso, htj⟩ := hTjIsog p D G L E gb w q r 𝔴 𝔫 S k T K₀ hLev i h hTj hInt u hu N' N (c * t) c
    hN'c hNc W _ o₁ o₂ n₁ n₂
  obtain ⟨x1q, hx1q⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ (T.M N').univ S.Y.univ S.M.univ C'.j S.π).1 C'.m S.mπ
  obtain ⟨x1c, hx1c⟩ := qcast (show C'.j ≫ S.π = 𝟙 _ ≫ (C'.j ≫ S.π) by simp) x1q
  obtain ⟨x1, hx1⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ (T.M N').univ o₁ S.M.univ (𝟙 _) (C'.j ≫ S.π)).2.2.1
    inferInstance n₁ x1c
  have hunit : IsUnit ((q : ℕ) : Γ((T.M N').X, ⊤)) := by
    have hqE : IsUnit (q : E) := (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero).isUnit
    simpa using hqE.map (((T.M N').s.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of E)).inv.hom)
  obtain ⟨y₀, ⟨hy₀, m₀, m₁, hm01⟩, -⟩ := Tj.univ _ (C'.j ≫ S.π) o₁ o₂ x1 ψ₀ hunit hiso htj
  obtain ⟨y, hys, hyg⟩ : ∃ y, y ≫ Lj.s = C'.j ∧ y ≫ Lj.g = y₀ :=
    ⟨_, Lj.pb.lift_fst _ _ hy₀.symm, Lj.pb.lift_snd _ _ hy₀.symm⟩
  obtain ⟨n'c, hn'c⟩ := qcast hys.symm C'.m
  obtain ⟨mm, hmm⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ (T.M N').univ Lj.o S.Y.univ y Lj.s).2.1 n'c Lj.ms
  obtain ⟨q1, hq1⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ W.o o₂ Tj.o' (𝟙 _) y₀).1 n₂ m₁
  obtain ⟨q1c, hq1c⟩ := qcast (show 𝟙 _ ≫ y₀ = y ≫ Lj.g by rw [hyg, Category.id_comp]) q1
  obtain ⟨q2, hq2⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ W.o Lj.o' Tj.o' y Lj.g).2.1 q1c Lj.m'
  obtain ⟨q3, hq3⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ W.o Lj.o' S.Y.univ y Lj.t).1 q2 Lj.mt
  obtain ⟨qC, hqC⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ (T.M N).univ S.Y.univ S.Y.univ C.j (𝟙 _)).2.2.2
    _ _ W.o W.π W.φ C.m
  obtain ⟨A1, hA1⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ (T.M N').univ Lj.o Tj.o y Lj.g).1 mm Lj.m₀
  obtain ⟨B1, hB1⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ (T.M N').univ o₁ Tj.o (𝟙 _) y₀).1 n₁ m₀
  obtain ⟨B1c, hB1c⟩ := qcast (show 𝟙 _ ≫ y₀ = y ≫ Lj.g by rw [hyg, Category.id_comp]) B1
  have I1 : mm.φ ≫ Lj.m₀.φ = n₁.φ ≫ m₀.φ := by
    rw [← hA1, ← hB1, ← hB1c]
    exact hQUniq q _ _ _ _ _ _ _ _ h3 hcq _ _ _ _ _ _ _ A1 B1c
  have I2 : mm.φ ≫ Lj.ψ.left = W.ψ.left ≫ q2.φ := by
    apply Lj.m'.cart.1.hom_ext
    · simp only [Category.assoc]
      rw [← Lj.sq, reassoc_of% I1, hm01, reassoc_of% hψ₀, ← hq2, hq1c, hq1]
    · simp only [Category.assoc, Over.w, mm.cart.1.w, q2.cart.1.w]
      rw [← Category.assoc (Over.Hom.left W.ψ), Over.w]
  have hIu : Integ L u := integ_of_mem ((hLev u).mp hu).1
  have hCu : CongId L S.𝔞 u := by
    have h1 := ((hLev u).mp hu).2
    rw [S.lev] at h1
    exact ((hCRT p D G L q r S.N₀ S.𝔞 hcq S.upow u hIu).1.mp h1).2
  have hCh : CongId L S.𝔞 h := hTj.other S.𝔞 S.sup S.upow
  have hx : ∀ y' : D.La, ∃ v ∈ LaHat D, (L.actG (h * u)) (inAf D ((algebraMap (𝓞 D.F) D.O) a • y')) =
      inAf D ((algebraMap (𝓞 D.F) D.O) a • y') + (N : ℕ) • v := by
    intro y'
    obtain ⟨v₁, hv₁, e₁⟩ := ((hCRT p D G L q r S.N₀ S.𝔞 hcq S.upow h hInt).2 a N hNpos N.2.2 hGen).mp hCh y'
    obtain ⟨v₂, hv₂, e₂⟩ := ((hCRT p D G L q r S.N₀ S.𝔞 hcq S.upow u hIu).2 a N hNpos N.2.2 hGen).mp hCu y'
    refine ⟨v₁ + L.actG h v₂, add_mem hv₁ (hInt v₂ hv₂), ?_⟩
    rw [map_mul, Module.End.mul_apply, e₂, map_add, map_nsmul, e₁, smul_add, add_assoc]
  have I4 : ∀ y' : D.La, ∀ l' : 𝟙_ (Over Lj.Z) ⟶ Lj.o.A, l'.left ≫ Lj.ms.φ = Lj.s ≫ (S.Y.lv y').left →
      ((T.M N').univ.eta (t • ((algebraMap (𝓞 D.F) D.O) a • y'))).left ≫ mm.φ = y ≫ l'.left := by
    intro y' l' hl'
    have hsm : (algebraMap (𝓞 D.F) D.O (↑t * a)) • y' = t • ((algebraMap (𝓞 D.F) D.O) a • y') := by
      rw [map_mul, map_natCast, mul_smul, Nat.cast_smul_eq_nsmul]
    apply Lj.ms.cart.1.hom_ext
    · simp only [Category.assoc]
      rw [← hmm, hn'c, hl', reassoc_of% hys, ← C'.lv, hsm]
    · simp only [Category.assoc]
      rw [mm.cart.1.w, reassoc_of% (sec_hom _), sec_hom l']
      simp
  have I3 : ∀ y' : D.La, (W.o.eta ((algebraMap (𝓞 D.F) D.O) a • y')).left ≫ q3.φ =
      (y ≫ Lj.t) ≫ (S.Y.lv y').left := by
    intro y'
    obtain ⟨l', hl'⟩ := sec_lift Lj.ms.cart.1 (S.Y.lv y')
    have hTE := hTrEta p D G L E gb (h * u) _ _ N' N (T.M N').univ W.o W.ψ W.trans N t 1 hN't
      (_root_.mul_one _).symm _ _ (hx y')
    rw [one_smul] at hTE
    have hlv := Lj.lev y' l' hl'
    rw [Over.comp_left, Category.assoc] at hlv
    rw [← hTE, Over.comp_left, hq3]
    simp only [Category.assoc]
    rw [← reassoc_of% I2, reassoc_of% (I4 y' l' hl'), hlv]
  obtain ⟨l, hlev, hl⟩ := hQLev q _ _ _ _ _ _ _ _ a S.𝔞 hNpos hGen _ _ _ W.o o₂ n₂
  obtain ⟨f₀, -, huniq⟩ := S.Y.rep _ _ o₂ l hlev
  obtain ⟨q3c, hq3c⟩ := qcast (show y ≫ Lj.t = 𝟙 _ ≫ (y ≫ Lj.t) by simp) q3
  obtain ⟨μ2, hμ2⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ W.o o₂ S.Y.univ (𝟙 _) (y ≫ Lj.t)).2.2.1
    inferInstance n₂ q3c
  obtain ⟨qCc, hqCc⟩ := qcast (show W.π ≫ C.j = 𝟙 _ ≫ (W.π ≫ C.j) by simp) qC
  obtain ⟨μ1, hμ1⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ W.o o₂ S.Y.univ (𝟙 _) (W.π ≫ C.j)).2.2.1
    inferInstance n₂ qCc
  have base2 : (y ≫ Lj.t) ≫ S.Y.s = (C'.j ≫ S.π) ≫ S.M.s := by
    simp only [Category.assoc]
    rw [← S.ov, reassoc_of% Lj.tπ, ← Tj.st, reassoc_of% hyg, reassoc_of% hy₀]
  have base1 : (W.π ≫ C.j) ≫ S.Y.s = (C'.j ≫ S.π) ≫ S.M.s := by
    rw [e0, Category.assoc, C.ov, reassoc_of% W.ov]
  have eq2 := huniq _ ⟨base2, μ2, fun y' => by
    rw [← hl y', Category.assoc, ← hμ2, hq3c, I3 y']⟩
  have eq1 := huniq _ ⟨base1, μ1, fun y' => by
    rw [← hl y', Category.assoc, ← hμ1, hqCc, hqC, ← Category.assoc]
    erw [W.φ.eta]
    rw [Category.assoc, C.lv, Category.assoc]⟩
  have yt : y ≫ Lj.t = W.π ≫ C.j := eq2.trans eq1.symm
  obtain ⟨q3y, hq3y⟩ := qcast yt q3
  refine ⟨⟨y, hys, yt, mm, ?_, ?_⟩⟩
  · rw [← hmm, hn'c]
  · rw [reassoc_of% I2, ← hq3, ← hqC, ← hq3y, hQUniq q _ _ _ _ _ _ _ _ h3 hcq _ _ _ _ _ _ _ q3y qC]
end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.HeckeLiftSeparatedOfLatticeCongruence
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open scoped TensorProduct

section Cart

variable {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

private theorem one_left_cart (hp : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : T ⟶ G').left ≫ φ = (1 : Over.mk (T.hom ≫ f) ⟶ G).left := by
  let x₀ : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ) (by
    have e := Over.w (1 : T ⟶ G')
    simp only [Over.mk_hom, Category.assoc, hp.1.w]
    rw [← Category.assoc, e])
  have h := hp.2 T 1 1 x₀ x₀ rfl rfl
  rw [_root_.mul_one] at h
  have h2 : x₀ * x₀ = x₀ := Over.OverMorphism.ext h
  have h3 : x₀ = 1 := by simpa using h2
  exact congrArg (fun g => g.left) h3

private theorem kill_iff (hp : IsGrpPullback G' G f φ) {T : Over S'} (x : T ⟶ G') :
    x = 1 ↔ x.left ≫ φ = (1 : Over.mk (T.hom ≫ f) ⟶ G).left := by
  constructor
  · rintro rfl
    exact one_left_cart hp T
  · intro h
    apply Over.OverMorphism.ext
    apply hp.1.hom_ext
    · rw [h, one_left_cart hp T]
    · rw [Over.w x, Over.w (1 : T ⟶ G')]

end Cart

private theorem one_left_congr {X Y : Scheme.{0}} {G : Over Y} [GrpObj G] {g g' : X ⟶ Y} (e : g = g') :
    (1 : Over.mk g ⟶ G).left = (1 : Over.mk g' ⟶ G).left := by
  subst e; rfl

private theorem kill_transfer {X Y : Scheme.{0}} {A B : Over Y} [GrpObj B] {g g' : X ⟶ Y} (e : g = g')
    (b : Over.mk g ⟶ A) (b' : Over.mk g' ⟶ A) (hl : b.left = b'.left) (ψ : A ⟶ B) :
    b ≫ ψ = 1 ↔ b' ≫ ψ = 1 := by
  subst e
  obtain rfl : b = b' := Over.OverMorphism.ext hl
  rfl

private theorem unit_left {X Y : Scheme.{0}} (e : Y ⟶ X) : (toUnit (Over.mk e)).left = e := by
  simpa using Over.w (toUnit (Over.mk e))

private theorem kill_chain {X' Z EX X P : Scheme.{0}} {A' Wo : Over X'} {o o' : Over Z} {U : Over EX} {B : Over X}
    [GrpObj o'] [GrpObj U] [GrpObj B] [GrpObj Wo]
    {y : X' ⟶ Z} {tt : Z ⟶ EX} {π : X' ⟶ X} {j : X ⟶ EX} {mφ : A'.left ⟶ o.left} {ψ₀ : o ⟶ o'}
    {mt : o'.left ⟶ U.left} {ψW : A' ⟶ Wo} {φ : Wo.left ⟶ B.left} {cm : B.left ⟶ U.left}
    (h1 : IsGrpPullback o' U tt mt) (h2 : IsGrpPullback Wo B π φ) (h3 : IsGrpPullback B U j cm)
    (hyt : y ≫ tt = π ≫ j) (hmt : mφ ≫ ψ₀.left ≫ mt = ψW.left ≫ φ ≫ cm)
    (e : P ⟶ X') (a : Over.mk e ⟶ A') (b : Over.mk (e ≫ y) ⟶ o) (hb : b.left = a.left ≫ mφ) :
    b ≫ ψ₀ = 1 ↔ a ≫ ψW = 1 := by
  have L : (b ≫ ψ₀).left ≫ mt = (a ≫ ψW).left ≫ φ ≫ cm := by
    simp only [Over.comp_left, Category.assoc, hb]
    rw [hmt]
  have E : (Over.mk (e ≫ y)).hom ≫ tt = (Over.mk e).hom ≫ π ≫ j := by
    simp only [Over.mk_hom, Category.assoc, hyt]
  rw [kill_iff h1, kill_iff (h2.comp h3), L, one_left_congr E]

section Grp

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G}

private theorem back_mul {h g : G.GAf} {m M : ℕ} (hb : ∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, L.actG h v' = m • v)
    (hd : m ∣ M) (hg : g ∈ L.KN 1) : ∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, L.actG (h * g) v' = M • v := by
  obtain ⟨d, rfl⟩ := hd
  intro v hv
  obtain ⟨v', hv', e⟩ := hb (d • v) (nsmul_mem hv d)
  refine ⟨L.actG g⁻¹ v', integ_of_mem (inv_mem hg) _ hv', ?_⟩
  have e1 : L.actG (h * g) (L.actG g⁻¹ v') = L.actG h v' := by
    rw [← Module.End.mul_apply, ← map_mul, _root_.mul_assoc, _root_.mul_inv_cancel, _root_.mul_one]
  rw [e1, e, mul_smul]

private theorem mod_iff {g g' : G.GAf} {M : ℕ} {x' : D.La} {x : D.La} {w : AfP p ⊗[ℚ] VQ D} (hg : Integ L g)
    (hw : w ∈ LaHat D) (hgg : L.actG (g * g') (inAf D x) = L.actG g (inAf D x' + M • w)) :
    (∃ v ∈ LaHat D, L.actG g (inAf D x') = M • v) ↔ ∃ v ∈ LaHat D, L.actG (g * g') (inAf D x) = M • v := by
  rw [hgg, map_add, map_nsmul]
  constructor
  · rintro ⟨v, hv, e⟩
    exact ⟨v + L.actG g w, add_mem hv (hg w hw), by rw [e, smul_add]⟩
  · rintro ⟨v, hv, e⟩
    refine ⟨v - L.actG g w, sub_mem hv (hg w hw), ?_⟩
    rw [smul_sub, ← e, add_sub_cancel_right]

end Grp

theorem UpperTheory.hecke_lift_separated_of_lattice_congruence :
    NumEx → BaseInv → TrEta → TrEtaPt → CongCRT → GrpLat → GrpCong → LiftSep := by
  intro hNum hBI hTr hPt hCRT hLat hCong p _ D G L E _ _ gb w q _ r 𝔴 𝔫 S k T K₀ hLev i h hi hTj hInt Tj Lj N' N
    t c a hN hNumN C' C hdvd u₁ hu₁ u₂ hu₂ v₁ hv₁ v₂ hv₂ W₁ W₂ V₁ V₂ l₁ l₂ Ω _ _ z hz
  have hpos : 0 < N'.1 := by have := N'.2.1; omega
  have hKN : ∀ {g}, g ∈ K₀ → g ∈ L.KN 1 := fun hg => ((hLev _).1 hg).1
  have hNum' : S.Num N'.1 (c * t) (t * a) := by
    rw [hN]
    exact (hNum p D E gb w q r 𝔴 𝔫 S N.1 (by have := N.2.1; omega)).2 c a t hNumN

  obtain ⟨C₂, hC₂⟩ : ∃ C₂ : S.Cl (T.M N').univ (c * t * 1) (((1 : ℕ) : 𝓞 D.F) * (t * a)), C₂.m.φ = C'.m.φ := by
    have : ∀ (c₁ : ℕ) (a₁ : 𝓞 D.F), c₁ = c * t * 1 → a₁ = ((1 : ℕ) : 𝓞 D.F) * (t * a) → ∀ C₁ : S.Cl (T.M N').univ c₁ a₁,
        ∃ C₂ : S.Cl (T.M N').univ (c * t * 1) (((1 : ℕ) : 𝓞 D.F) * (t * a)), C₂.m.φ = C₁.m.φ := by
      rintro _ _ rfl rfl C₁
      exact ⟨C₁, rfl⟩
    exact this _ _ (by simp) (by simp) C'
  have step : ∀ (u v : G.GAf), u ∈ K₀ → v ∈ K₀ → ∀ (W : Wit T (h * u) N' N) (V : Wit T v N' N') (l : Lift S T Lj W C' C) (x : D.La),
      ∃ b : Over.mk ((z ≫ V.π) ≫ l.y) ⟶ Lj.o.A, b.left ≫ Lj.ms.φ = z ≫ ((T.M N').univ.eta x).left ≫ C'.m.φ ∧
        (b ≫ Lj.ψ = 1 ↔ ∃ v' ∈ LaHat D, L.actG (h * u * v) (inAf D x) = N'.1 • v') := by
    intro u v hu hv W V l x
    obtain ⟨x', w', hw', e⟩ := GlobalTheory.T.latticeCompletion_eq_latticeVector_add_nsmul p D N'.1 hpos N'.2.2 (L.actG v (inAf D x))
      (integ_of_mem (hKN hv) _ (AddSubgroup.subset_closure ⟨1, x, fun v => by simp, rfl⟩))
    have hinv := (hBI p D G L E gb w q r 𝔴 𝔫 S k T K₀ hLev N' N' 1 (c * t) (t * a) (by simp) hNum' C₂ C' v hv V).2
    rw [hC₂] at hinv
    have htr := hTr p D G L E gb v (T.M N').X (T.M N').s N' N' (T.M N').univ V.o V.ψ V.trans N'.1 1 1 (by simp) (by simp) x x'
      ⟨w', hw', e⟩
    simp only [one_smul] at htr
    have hugInt : Integ L (h * u) := hInt.mul (integ_of_mem (hKN hu))
    let a₀ : Over.mk (z ≫ V.π) ⟶ (T.M N').univ.A := toUnit _ ≫ (T.M N').univ.eta x'
    have ha₀ : a₀.left = (z ≫ V.π) ≫ ((T.M N').univ.eta x').left := by
      simp only [a₀, Over.comp_left, unit_left]
    let b : Over.mk ((z ≫ V.π) ≫ l.y) ⟶ Lj.o.A := Over.homMk (a₀.left ≫ l.m.φ) (by
      have e1 := l.m.cart.1.w
      have e2 := Over.w a₀
      simp only [Over.mk_hom, Category.assoc] at e2 ⊢
      rw [e1, ← Category.assoc, e2, Category.assoc])
    refine ⟨b, ?_, ?_⟩
    · have e3 := V.φ.eta x'
      have e4 := congrArg (fun g => g.left) htr
      simp only [Over.comp_left] at e4
      show (a₀.left ≫ l.m.φ) ≫ Lj.ms.φ = _
      rw [Category.assoc, l.ms, ha₀, Category.assoc, Category.assoc, ← Category.assoc V.π, ← e3, ← e4]
      simp only [Category.assoc, hinv]
    · have hc := kill_chain (ψ₀ := Lj.ψ) (ψW := W.ψ) Lj.mt.cart W.φ.cart C.m.cart l.yt l.mt (z ≫ V.π) a₀ b rfl
      rw [hc]
      have := (hPt p D G L E gb (h * u) (T.M N').X (T.M N').s N' N (T.M N').univ W.o W.ψ W.trans Ω (z ≫ V.π) x').1
      rw [show a₀ ≫ W.ψ = _ from Category.assoc _ _ _, this]
      exact mod_iff hugInt hw' (by rw [map_mul, Module.End.mul_apply, e])
  have key : ∀ x : D.La, (∃ v ∈ LaHat D, L.actG (h * u₁ * v₁) (inAf D x) = N'.1 • v) ↔
      ∃ v ∈ LaHat D, L.actG (h * u₂ * v₂) (inAf D x) = N'.1 • v := by
    intro x
    obtain ⟨b₁, e₁, k₁⟩ := step u₁ v₁ hu₁ hv₁ W₁ V₁ l₁ x
    obtain ⟨b₂, e₂, k₂⟩ := step u₂ v₂ hu₂ hv₂ W₂ V₂ l₂ x
    have hy : (z ≫ V₁.π) ≫ l₁.y = (z ≫ V₂.π) ≫ l₂.y := by
      simpa only [Category.assoc] using hz
    have hl : b₁.left = b₂.left := by
      apply Lj.ms.cart.1.hom_ext
      · rw [e₁, e₂]
      · rw [Over.w b₁, Over.w b₂]
        exact hy
    rw [← k₁, ← k₂]
    exact kill_transfer hy b₁ b₂ hl Lj.ψ
  have hI₁ : Integ L (h * u₁ * v₁) := (hInt.mul (integ_of_mem (hKN hu₁))).mul (integ_of_mem (hKN hv₁))
  have hI₂ : Integ L (h * u₂ * v₂) := (hInt.mul (integ_of_mem (hKN hu₂))).mul (integ_of_mem (hKN hv₂))
  have hB₁ : ∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, L.actG (h * u₁ * v₁) v' = N'.1 • v := by
    rw [_root_.mul_assoc]
    exact back_mul hTj.back hdvd (mul_mem (hKN hu₁) (hKN hv₁))
  have hB₂ : ∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, L.actG (h * u₂ * v₂) v' = N'.1 • v := by
    rw [_root_.mul_assoc]
    exact back_mul hTj.back hdvd (mul_mem (hKN hu₂) (hKN hv₂))
  have hlat := hLat p D G L N'.1 hpos N'.2.2 (h * u₁ * v₁) (h * u₂ * v₂) hI₁ hI₂ hB₁ hB₂ key
  have hcg : CongId L 𝔫 h := by
    rw [S.lev]
    exact (hCRT p D G L q r S.N₀ S.𝔞 S.std.cop S.upow h hInt).1.2 ⟨hTj.away _ S.std.cop, hTj.other _ S.sup S.upow⟩
  have heq : h * (u₁ * v₁ * (u₂ * v₂)⁻¹) * h⁻¹ = h * u₁ * v₁ * (h * u₂ * v₂)⁻¹ := by group
  exact hCong p D G L 𝔫 K₀ hLev h _ hInt hcg (mul_mem (mul_mem hu₁ hv₁) (inv_mem (mul_mem hu₂ hv₂))) (heq ▸ hlat)
end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.LatticeGeneration
section
open UpperTheory.Gal.Int.Geo

namespace UpperTheory.ActionSupremumCommute

variable {A O M : Type} [CommRing A] [Ring O] [Algebra A O] [AddCommGroup M] [Module O M]

private lemma nat_act (N : ℕ) (y : M) : algebraMap A O (N : A) • y = N • y := by
  rw [map_natCast, Nat.cast_smul_eq_nsmul]

private lemma act_comm (c d : A) (y : M) :
    algebraMap A O c • algebraMap A O d • y = algebraMap A O d • algebraMap A O c • y := by
  rw [smul_smul, smul_smul, ← map_mul, ← map_mul, mul_comm c d]

private lemma exists_sup {a b : A} {N : ℕ} (hb : b ∈ Ideal.span {a} ⊔ Ideal.span {(N : A)}) :
    ∃ r s : A, b = r * a + s * (N : A) := by
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hb
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hu
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.mp hv
  exact ⟨r, s, rfl⟩

private lemma act_sup {a b : A} {N : ℕ} (hb : b ∈ Ideal.span {a} ⊔ Ideal.span {(N : A)}) (w : M) :
    ∃ y z : M, algebraMap A O b • w = algebraMap A O a • y + N • z := by
  obtain ⟨r, s, rfl⟩ := exists_sup hb
  refine ⟨algebraMap A O r • w, algebraMap A O s • w, ?_⟩
  rw [map_add, add_smul, map_mul, map_mul, mul_smul, mul_smul, act_comm r a, act_comm s (N : A), nat_act]

private lemma act_sup_of {a b : A} {N : ℕ} (hb : b ∈ Ideal.span {a} ⊔ Ideal.span {(N : A)})
    {y z : M} (hy : algebraMap A O a • y = N • z) :
    ∃ z' : M, algebraMap A O b • y = N • z' := by
  obtain ⟨r, s, rfl⟩ := exists_sup hb
  refine ⟨algebraMap A O r • z + algebraMap A O s • y, ?_⟩
  rw [map_add, add_smul, map_mul, map_mul, mul_smul, mul_smul, hy, nat_act, smul_add,
    smul_comm N (algebraMap A O r) z, smul_comm N (algebraMap A O s) y]

private lemma fwd {a : A} {N : ℕ} {𝔞 : Ideal A}
    (h : (Ideal.span {a} ⊔ Ideal.span {(N : A)}) * 𝔞 = Ideal.span {(N : A)})
    (inj : ∀ u v : M, N • u = N • v → u = v) (W : Submodule O M)
    (hW : ∀ c ∈ 𝔞, ∀ z : M, algebraMap A O c • z ∈ W) {y z : M}
    (hy : algebraMap A O a • y = N • z) : y ∈ W := by
  have key : ∀ t ∈ (Ideal.span {a} ⊔ Ideal.span {(N : A)}) * 𝔞,
      ∃ u ∈ W, algebraMap A O t • y = N • u := by
    intro t ht
    refine Submodule.mul_induction_on ht ?_ ?_
    · intro b hb c hc
      obtain ⟨z', hz'⟩ := act_sup_of hb hy
      refine ⟨algebraMap A O c • z', hW c hc z', ?_⟩
      rw [mul_comm b c, map_mul, mul_smul, hz']
      exact smul_comm _ _ _
    · rintro t t' ⟨u, hu, hu'⟩ ⟨v, hv, hv'⟩
      exact ⟨u + v, W.add_mem hu hv, by rw [map_add, add_smul, hu', hv', smul_add]⟩
  obtain ⟨u, hu, hu'⟩ := key (N : A) (by rw [h]; exact Ideal.mem_span_singleton_self _)
  rw [nat_act] at hu'
  rwa [inj y u hu']

private lemma bwd {a : A} {N : ℕ} {𝔞 : Ideal A}
    (h : (Ideal.span {a} ⊔ Ideal.span {(N : A)}) * 𝔞 = Ideal.span {(N : A)}) {y : M}
    (hy : y ∈ Submodule.span O {z : M | ∃ c ∈ 𝔞 ^ 1, ∃ z' : M, z = algebraMap A O c • z'}) :
    ∃ z : M, algebraMap A O a • y = N • z := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, z', rfl⟩ := hx
    rw [pow_one] at hc
    have hac : a * c ∈ Ideal.span {(N : A)} :=
      h ▸ Ideal.mul_mem_mul (Ideal.mem_sup_left (Ideal.mem_span_singleton_self a)) hc
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hac
    refine ⟨algebraMap A O t • z', ?_⟩
    rw [← mul_smul, ← map_mul, ← ht, map_mul, mul_smul, act_comm t (N : A), nat_act]
  | zero => exact ⟨0, by simp⟩
  | add x x' _ _ hx hx' =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hx'
    exact ⟨u + v, by rw [smul_add, hu, hv, smul_add]⟩
  | smul o x _ hx =>
    obtain ⟨u, hu⟩ := hx
    refine ⟨o • u, ?_⟩
    rw [← mul_smul, Algebra.commutes, mul_smul, hu]
    exact smul_comm _ _ _

private lemma part2 {a : A} {N : ℕ} {𝔞 : Ideal A}
    (h : (Ideal.span {a} ⊔ Ideal.span {(N : A)}) * 𝔞 = Ideal.span {(N : A)})
    (inj : ∀ u v : M, N • u = N • v → u = v) {x : M}
    (hx : ∀ c ∈ 𝔞, ∃ z : M, algebraMap A O c • x = N • z) :
    ∃ y z : M, x = algebraMap A O a • y + N • z := by
  have key : ∀ t ∈ (Ideal.span {a} ⊔ Ideal.span {(N : A)}) * 𝔞,
      ∃ y z : M, algebraMap A O t • x = N • (algebraMap A O a • y + N • z) := by
    intro t ht
    refine Submodule.mul_induction_on ht ?_ ?_
    · intro b hb c hc
      obtain ⟨z0, hz0⟩ := hx c hc
      obtain ⟨y, z, hyz⟩ := act_sup (O := O) hb z0
      refine ⟨y, z, ?_⟩
      rw [map_mul, mul_smul, hz0, ← hyz]
      exact smul_comm _ _ _
    · rintro t t' ⟨y, z, h1⟩ ⟨y', z', h2⟩
      refine ⟨y + y', z + z', ?_⟩
      rw [map_add, add_smul, h1, h2]
      simp only [smul_add]
      abel
  obtain ⟨y, z, hyz⟩ := key (N : A) (by rw [h]; exact Ideal.mem_span_singleton_self _)
  rw [nat_act] at hyz
  exact ⟨y, z, inj _ _ hyz⟩

end UpperTheory.ActionSupremumCommute

theorem UpperTheory.lattice_generation :
    LatGen := by
  intro q _ D a N 𝔞 hN hG
  haveI := D.freeLa
  have inj : ∀ u v : D.La, N • u = N • v → u = v := by
    intro u v huv
    have h0 : (N : ℤ) • (u - v) = 0 := by
      rw [smul_sub, natCast_zsmul, natCast_zsmul, huv, sub_self]
    rcases smul_eq_zero.mp h0 with h1 | h1
    · exact absurd (Int.natCast_eq_zero.mp h1) hN.ne'
    · exact sub_eq_zero.mp h1
  refine ⟨fun y => ⟨fun ⟨z, hz⟩ => UpperTheory.ActionSupremumCommute.fwd hG inj _ ?_ hz,
    fun hy => UpperTheory.ActionSupremumCommute.bwd hG hy⟩, fun x hx => UpperTheory.ActionSupremumCommute.part2 hG inj hx⟩
  intro c hc z
  exact Submodule.subset_span ⟨c, by rwa [pow_one], z, rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.PowerProjectorExists
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open UpperTheory.Gal.Int.Geo

private theorem relDim_pow {S : Scheme.{0}} (A : Over S) (g : ℕ) (hg : SmoothOfRelativeDimension g A.hom) (k : ℕ) :
    SmoothOfRelativeDimension (k * g) (GlobalTheory.KS.pow A k).hom := by
  induction k with
  | zero =>
    obtain ⟨h0, -⟩ := UpperTheory.iteratedFiberPower_zero_isIso_and_succ_isPullback A
    simp only [zero_mul]
    infer_instance
  | succ m ih =>
    obtain ⟨-, hs⟩ := UpperTheory.iteratedFiberPower_zero_isIso_and_succ_isPullback A
    obtain ⟨u, v, hpb, hcomp⟩ := hs m
    have hu : SmoothOfRelativeDimension g u :=
      (smoothOfRelativeDimension_isStableUnderBaseChange (n := g)).of_isPullback hpb.flip hg
    rw [← hcomp, Nat.succ_mul, Nat.add_comm]
    infer_instance

theorem UpperTheory.power_projector_exists :
    PowProj := by
  intro q _ D R _ _ b N _ _ X s o k
  letI := o.grp
  haveI := o.comm
  have hT := GlobalTheory.T.harrisTaylor_relDim_and_diagonal_isLineBundle q D R b N X s o
  refine ⟨fun hs => GlobalTheory.KS.isProjOver_pow R X s hs o.A o.ab _ hT.2 o.ample k, ?_⟩
  intro d hd
  haveI := relDim_pow o.A D.g hT.1 k
  exact ⟨k * D.g + d, inferInstance⟩
end


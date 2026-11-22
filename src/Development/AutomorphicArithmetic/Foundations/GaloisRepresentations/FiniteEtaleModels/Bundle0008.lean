import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.Bundle0006
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3164
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedCommGroupSchemeArtinFibreProduct
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.Bundle0004

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsUnitNatOf
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.crystallineComparison.Mod (Std TjD KerAt)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

private theorem isUnit_nat_of {E : Type} [Field E] [CharZero E] {V : Scheme.{0}} (s : V ⟶ Sp E) (n : ℕ) (hn : n ≠ 0) :
    IsUnit ((n : ℕ) : Γ(V, ⊤)) := by
  have hE : IsUnit ((n : E)) := (Nat.cast_ne_zero.mpr hn).isUnit
  have h1 : IsUnit ((n : Γ(Sp E, ⊤))) := by
    have := hE.map (Scheme.ΓSpecIso (CommRingCat.of E)).inv.hom
    simpa using this
  have := h1.map s.appTop.hom
  simpa using this

section
variable {q : ℕ} [Fact q.Prime] {D : Datum q} {R R' : Type} [CommRing R] [CommRing R'] [Algebra ℚ R'] {b : Base D R}
  {gb : GBase D.toG R'}

private theorem qmap_cast {N₁ N c : ℕ} {V Y : Scheme.{0}} {s : V ⟶ Sp R'} {t : Y ⟶ Sp R} {a : GObj gb N₁ s} {u : Obj b N t}
    {f f' : V ⟶ Y} (h : f = f') (n : QMap a u f c) : ∃ n' : QMap a u f' c, n'.φ = n.φ := by
  subst h
  exact ⟨n, rfl⟩

private theorem rigid_of (hO : UpperTheory.Gal.crystallineComparison.Mod.ObjTri) {N : ℕ} (hN : 3 ≤ N) (hNq : N.Coprime q) {S₁ S₂ : Scheme.{0}}
    {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {o₁ : Obj b N s₁} {o₂ : Obj b N s₂} {f f' : S₁ ⟶ S₂}
    (m : ObjMap o₁ o₂ f) (m' : ObjMap o₁ o₂ f') (h : f = f') : m.φ = m'.φ := by
  subst h
  exact (hO q D R b N hN hNq S₁ S₂ S₂ s₁ s₂ s₂ o₁ o₂ o₂ f (𝟙 _)).1 m m'

private theorem read_tj {N : ℕ} {M : Model b N} {r : ℤ} {w : Ideal (𝓞 D.F)} {j c : ℕ} (Tj : TjD M r w j c) {V : Scheme.{0}}
    (x : V ⟶ M.X) (s₀ : V ⟶ Sp R) (hx : x ≫ M.s = s₀) (o₁ o₂ : Obj b N s₀) (m : ObjMap o₁ M.univ x) (ψ₀ : o₁.A ⟶ o₂.A)
    (hu : IsUnit ((q : ℕ) : Γ(V, ⊤))) (hi : ES.IsPIsog c o₁ o₂ ψ₀) (ht : ES.IsTj r w j o₁ o₂ ψ₀) :
    ∃ (y : V ⟶ Tj.Y) (_ : y ≫ Tj.s = x) (m₀ : ObjMap o₁ Tj.o y) (m₁ : ObjMap o₂ Tj.o' y),
      m₀.φ ≫ Tj.ψ.left = ψ₀.left ≫ m₁.φ := by
  subst hx
  obtain ⟨y, ⟨hy, m₀, m₁, h⟩, -⟩ := Tj.univ V x o₁ o₂ m ψ₀ hu hi ht
  exact ⟨y, hy, m₀, m₁, h⟩

private theorem read_core (hQ : QComp) (hO : UpperTheory.Gal.crystallineComparison.Mod.ObjTri) {N N₁ N₂ c₁ c₂ : ℕ} (hN : 3 ≤ N) (hNq : N.Coprime q)
    {M : Model b N} {r : ℤ} {w : Ideal (𝓞 D.F)} {j c : ℕ} (Tj : TjD M r w j c)
    {V Y₁ Y₂ : Scheme.{0}} {s : V ⟶ Sp R'} {s₀ : V ⟶ Sp R} {t₁ : Y₁ ⟶ Sp R} {t₂ : Y₂ ⟶ Sp R}
    {a : GObj gb N₁ s} {a' : GObj gb N₂ s} {o₁ o₂ : Obj b N s₀} {u₁ : Obj b N t₁} {u₂ : Obj b N t₂}
    (n₁ : QMap a o₁ (𝟙 V) c₁) (n₂ : QMap a' o₂ (𝟙 V) c₂) {j₁ : V ⟶ Y₁} {j₂ : V ⟶ Y₂}
    (k₁ : QMap a u₁ j₁ c₁) (k₂ : QMap a' u₂ j₂ c₂) {f : Y₁ ⟶ M.X} {π : Y₂ ⟶ M.X}
    (mf : ObjMap u₁ M.univ f) (mπ : ObjMap u₂ M.univ π)
    (hb₁ : (j₁ ≫ f) ≫ M.s = s₀) (hb₂ : (j₂ ≫ π) ≫ M.s = s₀)
    (ψ' : a.A.left ⟶ a'.A.left) (ψ₀ : o₁.A ⟶ o₂.A) (hψ : n₁.φ ≫ ψ₀.left = ψ' ≫ n₂.φ)
    (hu : IsUnit ((q : ℕ) : Γ(V, ⊤))) (hi : ES.IsPIsog c o₁ o₂ ψ₀) (ht : ES.IsTj r w j o₁ o₂ ψ₀) :
    ∃ (y : V ⟶ Tj.Y) (fa : a.A.left ⟶ Tj.o.A.left) (fb : a'.A.left ⟶ Tj.o'.A.left),
      y ≫ Tj.s = j₁ ≫ f ∧ y ≫ Tj.t = j₂ ≫ π ∧ IsGrpPullback a.A Tj.o.A y fa ∧ IsGrpPullback a'.A Tj.o'.A y fb ∧
      fa ≫ Tj.ψ.left = ψ' ≫ fb ∧ fa ≫ Tj.ms.φ = k₁.φ ≫ mf.φ ∧ fb ≫ Tj.mt.φ = k₂.φ ≫ mπ.φ := by
  obtain ⟨k₁', hk₁'⟩ := qmap_cast (Category.id_comp j₁).symm k₁
  obtain ⟨k₂', hk₂'⟩ := qmap_cast (Category.id_comp j₂).symm k₂
  obtain ⟨m₁, hm₁⟩ := (hQ q D R R' b gb N₁ N c₁ V V Y₁ s s₀ t₁ a o₁ u₁ (𝟙 V) j₁).2.2.1 inferInstance n₁ k₁'
  obtain ⟨m₂, hm₂⟩ := (hQ q D R R' b gb N₂ N c₂ V V Y₂ s s₀ t₂ a' o₂ u₂ (𝟙 V) j₂).2.2.1 inferInstance n₂ k₂'
  obtain ⟨mx, hmx⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m₁ mf
  obtain ⟨mz, hmz⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m₂ mπ
  obtain ⟨y, hy, m₀, m', hsq⟩ := read_tj Tj (j₁ ≫ f) s₀ hb₁ o₁ o₂ mx ψ₀ hu hi ht
  obtain ⟨e₁, he₁⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m' Tj.mt
  obtain ⟨e₀, he₀⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m₀ Tj.ms
  have hbt : (y ≫ Tj.t) ≫ M.s = s₀ := by
    rw [Category.assoc, ← Tj.st, ← Category.assoc, hy, hb₁]
  have yt : y ≫ Tj.t = j₂ ≫ π := (M.rep V s₀ o₂).unique ⟨hbt, ⟨e₁⟩⟩ ⟨hb₂, ⟨mz⟩⟩
  obtain ⟨p₁, hp₁⟩ := (hQ q D R R' b gb N₁ N c₁ V V Tj.Y s s₀ (Tj.s ≫ M.s) a o₁ Tj.o (𝟙 V) y).1 n₁ m₀
  obtain ⟨p₂, hp₂⟩ := (hQ q D R R' b gb N₂ N c₂ V V Tj.Y s s₀ (Tj.s ≫ M.s) a' o₂ Tj.o' (𝟙 V) y).1 n₂ m'
  have r₀ : m₀.φ ≫ Tj.ms.φ = m₁.φ ≫ mf.φ := by
    rw [← he₀, ← hmx]
    exact rigid_of hO hN hNq e₀ mx hy
  have r₁ : m'.φ ≫ Tj.mt.φ = m₂.φ ≫ mπ.φ := by
    rw [← he₁, ← hmz]
    exact rigid_of hO hN hNq e₁ mz yt
  refine ⟨y, n₁.φ ≫ m₀.φ, n₂.φ ≫ m'.φ, hy, yt, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨p₁', hp₁'⟩ := qmap_cast (Category.id_comp y) p₁
    have := p₁'.cart
    rw [hp₁', hp₁] at this
    exact this
  · obtain ⟨p₂', hp₂'⟩ := qmap_cast (Category.id_comp y) p₂
    have := p₂'.cart
    rw [hp₂', hp₂] at this
    exact this
  · rw [Category.assoc, hsq, ← Category.assoc, hψ, Category.assoc]
  · rw [Category.assoc, r₀, ← Category.assoc, ← hm₁, hk₁']
  · rw [Category.assoc, r₁, ← Category.assoc, ← hm₂, hk₂']

end

theorem UpperTheory.Gal.FiniteEtaleModels.bRead_of :
    IsogG → QObj → QComp → UpperTheory.Gal.crystallineComparison.Mod.ObjTri → BRead := by
  intro hI hQO hQC hO p _ D G L _ E _ _ gb w q _ r 𝔴 𝔫 S k T N₀ 𝔟₁ 𝔟₂ X₁ X₂ 𝔴' i hmax hu hle hin h hint htj M₁ M₂ c₁ c₂ a₁ a₂ hn₁ hn₂
    C₁ C₂ W f mf hf e he he0 Tj
  have h3 : 3 ≤ N₀ := X₁.lev.1
  have hcq : N₀.Coprime q := X₁.lev.2.1
  have hM₁ : M₁.1 = N₀ * c₁ := hn₁.1
  have hM₂ : M₂.1 = N₀ * c₂ := hn₂.1
  have pos₁ : 0 < M₁.1 := by have := M₁.2.1; omega
  have pos₂ : 0 < M₂.1 := by have := M₂.2.1; omega
  obtain ⟨o₁, ⟨n₁⟩⟩ := hQO q (datAt S.atq S.sp) (Ow w) E S.b gb (algebraMap (Ow w) E) S.mat M₁.1 N₀ c₁ hM₁ pos₁ hcq _ _ (T.M M₁).univ
  obtain ⟨o₂, ⟨n₂⟩⟩ := hQO q (datAt S.atq S.sp) (Ow w) E S.b gb (algebraMap (Ow w) E) S.mat M₂.1 N₀ c₂ hM₂ pos₂ hcq _ _ W.o
  obtain ⟨ψ₀, hψ, hi, ht⟩ := hI p D G L E gb q r 𝔴 𝔴' S.atq S.sp S.std.m1 hmax hu (Ow w) S.b N₀ hcq i e he h 1 htj hint (one_mem _) M₁ M₂ c₁ c₂
    hM₁ hM₂ _ _ (T.M M₁).univ W.o W.ψ (by rw [_root_.mul_one]; exact W.trans) _ o₁ o₂ n₁ n₂
  obtain ⟨k₂, hk₂⟩ := (hQC q (datAt S.atq S.sp) (Ow w) E S.b gb M₂.1 N₀ c₂ (T.M M₂).X X₂.Y.X X₂.Y.X (T.M M₂).s X₂.Y.s X₂.Y.s
    (T.M M₂).univ X₂.Y.univ X₂.Y.univ C₂.j (𝟙 _)).2.2.2 _ (T.M M₁).s W.o W.π W.φ C₂.m
  have hb₁ : (C₁.j ≫ f) ≫ X₂.M.s = (T.M M₁).s ≫ spMap (algebraMap (Ow w) E) := by
    rw [Category.assoc, hf]
    exact C₁.ov
  have hb₂ : ((W.π ≫ C₂.j) ≫ X₂.π) ≫ X₂.M.s = (T.M M₁).s ≫ spMap (algebraMap (Ow w) E) := by
    rw [Category.assoc, Category.assoc, X₂.ov]
    refine (congrArg (W.π ≫ ·) C₂.ov).trans ?_
    simp only [← Category.assoc, W.ov]
  have hun : IsUnit ((q : ℕ) : Γ((T.M M₁).X, ⊤)) := isUnit_nat_of (T.M M₁).s q (Fact.out : q.Prime).ne_zero
  obtain ⟨y, fa, fb, ys, yt, ca, cb, sq, ms, mt⟩ := read_core hQC hO h3 hcq Tj n₁ n₂ C₁.m k₂ mf X₂.mπ hb₁ hb₂ W.ψ.left ψ₀ hψ hun hi ht
  exact ⟨⟨y, ys, by rw [yt, Category.assoc], fa, fb, ca, cb, sq, ms, by rw [mt, hk₂, Category.assoc]⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.KerAtLift
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.crystallineComparison.Mod (Std TjD KerAt)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

namespace UpperTheory.Gal.FiniteEtaleModels

section
variable {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

private theorem pt_one_iff (h : IsGrpPullback G' G f φ) {T : Over S'} (x : T ⟶ G') (x₀ : Over.mk (T.hom ≫ f) ⟶ G)
    (e : x₀.left = x.left ≫ φ) : x = 1 ↔ x₀ = 1 := by
  constructor
  · rintro rfl
    exact Over.OverMorphism.ext (by rw [e, GlobalTheory.GlueGrpLaw.one_left h T])
  · intro h0
    refine Over.OverMorphism.ext (h.1.hom_ext ?_ ?_)
    · rw [← e, h0, GlobalTheory.GlueGrpLaw.one_left h T]
    · rw [Over.w x, Over.w (1 : T ⟶ G')]

end

section
variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {M : Model b N} {r : ℤ}
  {w : Ideal (𝓞 D.F)} {j c : ℕ}

private theorem kerAt_lift (T : TjD M r w j c) {X : Scheme.{0}} (z : X ⟶ T.Y) (a' : Over.mk z ⟶ T.o.A) :
    KerAt T z (a'.left ≫ T.ms.φ) ↔ a' ≫ T.ψ = 1 := by
  refine ⟨fun h => h a' rfl, fun h b hb => ?_⟩
  have : b = a' := Over.OverMorphism.ext (T.ms.cart.1.hom_ext hb (by rw [Over.w b, Over.w a']))
  rw [this]; exact h

end

section
variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G} {E : Type} [Field E] [NumberField E] {gb : GBase D.toG E}
  {w : HeightOneSpectrum (𝓞 E)} {q : ℕ} [Fact q.Prime] {r : ℤ} {𝔴 𝔫 : Ideal (𝓞 D.F)} {S : Site gb w q r 𝔴 𝔫} {k : ℕ} {T : KS L gb k}
  {N₀ : ℕ} {𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)} {X₁ : Ext S N₀ 𝔟₁} {X₂ : Ext S N₀ 𝔟₂} {𝔴' : Ideal (𝓞 D.F)} {i : ℕ} {h : G.GAf} {M₁ M₂ : Lv p}
  {c₁ c₂ : ℕ} {a₁ a₂ : 𝓞 D.F}

private theorem ker_read {C₁ : X₁.site.Cl (T.M M₁).univ c₁ a₁} {C₂ : X₂.site.Cl (T.M M₂).univ c₂ a₂} {W : Wit T h M₁ M₂}
    {f : X₁.Y.X ⟶ X₂.M.X} {mf : ObjMap X₁.Y.univ X₂.M.univ f} {c : ℕ} {Tj : TjD X₂.M r 𝔴' i c} (P : BPt C₁ C₂ W mf Tj)
    {Ω : Type} [Field Ω] (z : Sp Ω ⟶ (T.M M₁).X) (e : 𝟙_ (Over (T.M M₁).X) ⟶ (T.M M₁).univ.A) :
    KerAt Tj (z ≫ P.y) (z ≫ e.left ≫ C₁.m.φ ≫ mf.φ) ↔ toUnit (Over.mk z) ≫ e ≫ W.ψ = 1 := by
  let a' : Over.mk (z ≫ P.y) ⟶ Tj.o.A := Over.homMk (z ≫ e.left ≫ P.fa) (by
    have h1 : e.left ≫ (T.M M₁).univ.A.hom = 𝟙 _ := Over.w e
    simp only [Over.mk_hom, Category.assoc]
    rw [P.ca.1.w, reassoc_of% h1])
  have h1 := kerAt_lift Tj (z ≫ P.y) a'
  have h2 : a'.left ≫ Tj.ms.φ = z ≫ e.left ≫ C₁.m.φ ≫ mf.φ := by
    simp only [a', Over.homMk_left, Category.assoc, P.ms]
  rw [h2] at h1
  rw [h1]
  refine (pt_one_iff P.cb (toUnit (Over.mk z) ≫ e ≫ W.ψ) (a' ≫ Tj.ψ) ?_).symm
  simp only [a', Over.comp_left, Over.homMk_left, Category.assoc, P.sq]
  simp

end

section
variable {q : ℕ} [Fact q.Prime] {D : Datum q} {R R' : Type} [CommRing R] [CommRing R'] [Algebra ℚ R'] {b : Base D R} {gb : GBase D.toG R'}
  {N₀ N₁ : ℕ} {𝔟 𝔴' : Ideal (𝓞 D.F)}

private theorem cls_read (hb : 𝔟 ≤ 𝔴') (Y : EtModel b N₀ 𝔟 1) (M : Model b N₀) {f : Y.X ⟶ M.X} (mf : ObjMap Y.univ M.univ f)
    {X : Scheme.{0}} {s : X ⟶ Sp R'} {o : GObj gb N₁ s} {β : R →+* R'} {c : ℕ} {a : 𝓞 D.F} (C : Cls Y β o c a)
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ X) (g : Over.mk ((x ≫ C.j) ≫ f) ⟶ M.univ.A)
    (hg : ES.KilledBy M.univ 𝔴' g) :
    ∃ d : D.La, ∀ z : Sp Ω ⟶ X, z ≫ C.j = x ≫ C.j → g.left = z ≫ (o.eta d).left ≫ C.m.φ ≫ mf.φ := by
  let g₁ : Over.mk (x ≫ C.j) ⟶ Y.univ.A :=
    Over.homMk (mf.cart.1.lift g.left (x ≫ C.j) (Over.w g)) (by simp)
  have hg₁ : g₁.left ≫ mf.φ = g.left := by simp [g₁]
  have hk : ∀ c ∈ 𝔟 ^ 1, g₁ ≫ Y.univ.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := fun c hc => by
    refine (pt_one_iff mf.cart _ (g ≫ M.univ.act.act (algebraMap (𝓞 D.F) D.O c)) ?_).2 (hg c (hb (by simpa using hc)))
    simp only [Over.comp_left, Category.assoc]
    rw [mf.act, ← Category.assoc, hg₁]
  obtain ⟨y, hy⟩ := (Y.isLev.2.2.2 Ω (x ≫ C.j)).2 g₁ hk
  refine ⟨algebraMap (𝓞 D.F) D.O a • y, fun z hz => ?_⟩
  have hl := C.lv y
  rw [← hg₁, ← hy, reassoc_of% hl, reassoc_of% hz]
  simp [Over.toUnit_left]

end

end UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.bKer_of :
    SecInjG → TrEtaPt → BKer := by
  intro hS hT p _ D G L hSc E _ _ gb w q _ r 𝔴 𝔫 S k T N₀ 𝔟₁ 𝔟₂ X₁ X₂ 𝔴' i hmax hu hb hi h hint htj M₁ M₂ c₁ c₂ a₁ a₂ hn₁ hn₂ C₁ C₂ W f mf hf
    e he hpos Tj P Ω _ _ x x' hxx'
  haveI : CharZero Ω :=
    charZero_of_injective_ringHom (Spec.preimage (x ≫ (T.M M₁).s)).hom.injective
  have hb' : 𝔟₁ ≤ 𝔴' := hb.trans Ideal.mul_le_right
  refine hS q (datAt S.atq S.sp) (Ow w) S.b N₀ X₂.lev.1 X₂.lev.2.1 hSc.m1 r 𝔴' i e hmax hu hi hpos X₂.M Tj Ω ((x ≫ C₁.j) ≫ f)
    (x ≫ P.y) (x' ≫ P.y) ?_ ?_ ?_
  · rw [Category.assoc, Category.assoc, P.ys]
  · rw [Category.assoc, P.ys, ← Category.assoc, hxx', Category.assoc]
  intro g hg
  obtain ⟨d, hd⟩ := cls_read (D := datAt S.atq S.sp) hb' X₁.Y X₂.M mf C₁ x g hg
  have k₁ : KerAt Tj (x ≫ P.y) g.left ↔ toUnit (Over.mk x) ≫ (T.M M₁).univ.eta d ≫ W.ψ = 1 := by
    rw [hd x rfl]; exact ker_read P x _
  have k₂ : KerAt Tj (x' ≫ P.y) g.left ↔ toUnit (Over.mk x') ≫ (T.M M₁).univ.eta d ≫ W.ψ = 1 := by
    rw [hd x' hxx'.symm]; exact ker_read P x' _
  exact k₁.trans (((hT p D G L E gb h (T.M M₁).X (T.M M₁).s M₁ M₂ (T.M M₁).univ W.o W.ψ W.trans Ω x d).1.trans
    (hT p D G L E gb h (T.M M₁).X (T.M M₁).s M₁ M₂ (T.M M₁).univ W.o W.ψ W.trans Ω x' d).1.symm).trans k₂.symm)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.OEpsEx
section
theorem UpperTheory.Gal.FiniteEtaleModels.O.epsEx :
    UpperTheory.Gal.FiniteEtaleModels.O.EpsEx := by
  intro A _ _ _ 𝔟₁ 𝔟₂ a₁ a₂ M₁ M₂ t hpos hM hle h₁ h₂
  unfold UpperTheory.Gal.Int.Geo.IsGen at h₁ h₂
  have hM1 : (M₁ : A) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
  have hMc : (M₁ : A) = (t : A) * (M₂ : A) := by rw [hM]; push_cast; ring
  set I₁ := Ideal.span {a₁} ⊔ Ideal.span {(M₁ : A)} with hI₁
  have hI₁0 : I₁ ≠ ⊥ := by
    intro h
    have hmem : (M₁ : A) ∈ I₁ := Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
    rw [h, Ideal.mem_bot] at hmem
    exact hM1 hmem
  have h𝔟0 : 𝔟₁ ≠ ⊥ := by
    intro h
    rw [h, Ideal.mul_bot, eq_comm, Ideal.span_singleton_eq_bot] at h₁
    exact hM1 h₁
  have hkey : ∀ {J : Ideal A}, J * 𝔟₂ ≤ Ideal.span {(M₁ : A)} → J ≤ I₁ := by
    intro J hJ
    have h3 : J * 𝔟₁ ≤ I₁ * 𝔟₁ := by
      rw [h₁]
      exact le_trans (Ideal.mul_mono_right hle) hJ
    rw [← Ideal.dvd_iff_le] at h3 ⊢
    exact (mul_dvd_mul_iff_right h𝔟0).mp h3
  have hta : (t : A) * a₂ ∈ I₁ := by
    have hsp : Ideal.span {(t : A) * a₂} ≤ I₁ := by
      apply hkey
      rw [← Ideal.span_singleton_mul_span_singleton, mul_assoc, hMc,
        ← Ideal.span_singleton_mul_span_singleton, ← h₂]
      exact Ideal.mul_mono_right (Ideal.mul_mono_left le_sup_left)
    exact hsp (Ideal.mem_span_singleton_self _)
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hta
  obtain ⟨ε, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hz
  refine ⟨ε, ⟨-d, by rw [← hyz]; ring⟩, ?_⟩
  have hJK : I₁ * Ideal.span {ε} ⊔ Ideal.span {(M₁ : A)} =
      Ideal.span {(t : A)} * (Ideal.span {a₂} ⊔ Ideal.span {(M₂ : A)}) := by
    rw [Ideal.mul_sup, Ideal.span_singleton_mul_span_singleton,
      Ideal.span_singleton_mul_span_singleton, ← hMc, hI₁, Ideal.sup_mul,
      Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_mul_span_singleton]
    apply le_antisymm
    · refine sup_le (sup_le ?_ ?_) le_sup_right
      · rw [Ideal.span_singleton_le_iff_mem]
        have hae : a₁ * ε = (t : A) * a₂ - d * M₁ := by rw [← hyz]; ring
        rw [hae]
        exact Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
          (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
      · rw [Ideal.span_singleton_le_iff_mem]
        exact Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    · refine sup_le ?_ le_sup_right
      rw [Ideal.span_singleton_le_iff_mem, ← hyz]
      refine Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_sup_left ?_))
        (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
      rw [mul_comm]
      exact Ideal.mem_span_singleton_self _
  apply mul_left_cancel₀ hI₁0
  rw [h₁, ← mul_assoc, Ideal.mul_sup, h₁, hJK, mul_assoc, h₂,
    Ideal.span_singleton_mul_span_singleton, ← hMc]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.OLiftUnit
section
set_option autoImplicit false

namespace UpperTheory.Gal.FiniteEtaleModels.O.LU

private theorem exists_sep {A : Type} [CommRing A] [IsDedekindDomain A] (u 𝔞 : Ideal A) (hu : u ≠ ⊥) :
    ∃ s t : A, s ∈ 𝔞 ∧ s + t = 1 ∧ ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → u ≤ 𝔪 → ¬ 𝔞 ≤ 𝔪 → t ∈ 𝔪 := by
  classical
  have hfin := Ideal.finite_factors (R := A) hu
  let S := hfin.toFinset.filter (fun v => ¬ 𝔞 ≤ v.asIdeal)
  have hc : IsCoprime 𝔞 (∏ v ∈ S, v.asIdeal) := by
    apply IsCoprime.prod_right
    intro v hv
    have hm : v.asIdeal.IsMaximal := v.isMaximal
    rw [Ideal.isCoprime_iff_sup_eq]
    exact hm.out.2 _ (right_lt_sup.2 (Finset.mem_filter.1 hv).2)
  obtain ⟨s, hs, t, ht, hst⟩ := Ideal.isCoprime_iff_exists.1 hc
  refine ⟨s, t, hs, hst, fun 𝔪 hm hum ha => ?_⟩
  have hne : 𝔪 ≠ ⊥ := fun h => hu (le_bot_iff.1 (h ▸ hum))
  let v : IsDedekindDomain.HeightOneSpectrum A := ⟨𝔪, hm.isPrime, hne⟩
  have hv : v ∈ S := by
    refine Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 ?_, ha⟩
    exact Ideal.dvd_iff_le.2 hum
  exact Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun v : IsDedekindDomain.HeightOneSpectrum A => v.asIdeal) hv) ht

private theorem sup_range_pow {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    (g : M →ₗ[A] M) (u : Ideal A)
    (h : ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → u ≤ 𝔪 → LinearMap.range g ⊔ (𝔪 • ⊤ : Submodule A M) = ⊤) (e : ℕ) :
    LinearMap.range g ⊔ (u ^ e • ⊤ : Submodule A M) = ⊤ := by
  set R := LinearMap.range g with hR
  let I : Ideal A := Module.annihilator A (M ⧸ R)
  have hIu : I ⊔ u ^ e = ⊤ := by
    by_contra hne
    obtain ⟨𝔪, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    have hum : u ≤ 𝔪 := hm.isPrime.le_of_pow_le (le_sup_right.trans hle)
    have hQ : (⊤ : Submodule A (M ⧸ R)) ≤ 𝔪 • ⊤ := by
      intro y _
      obtain ⟨x, rfl⟩ := R.mkQ_surjective y
      have hx : x ∈ R ⊔ (𝔪 • ⊤ : Submodule A M) := by rw [h 𝔪 hm hum]; trivial
      obtain ⟨r, hr, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
      have h1 : R.mkQ (r + z) = R.mkQ z := by
        rw [map_add, show R.mkQ r = 0 from (Submodule.Quotient.mk_eq_zero R).2 hr, zero_add]
      rw [h1]
      have h2 := Submodule.mem_map_of_mem (f := R.mkQ) hz
      rw [Submodule.map_smul''] at h2
      simpa using h2
    obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul 𝔪 ⊤
      Module.Finite.fg_top hQ
    have hrI : r ∈ I := Module.mem_annihilator.2 fun y => hr y trivial
    have hrm : r ∈ 𝔪 := hle (Ideal.mem_sup_left hrI)
    exact hm.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using sub_mem hrm hr1))
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (hIu ▸ (Submodule.mem_top : (1 : A) ∈ ⊤))
  have h1 : a • x ∈ R := by
    have : a • R.mkQ x = 0 := Module.mem_annihilator.1 ha _
    rw [← map_smul] at this
    exact (Submodule.Quotient.mk_eq_zero R).1 this
  have h2 : b • x ∈ (u ^ e • ⊤ : Submodule A M) := Submodule.smul_mem_smul hb trivial
  have h3 : x = a • x + b • x := by rw [← add_smul, hab, one_smul]
  rw [h3]
  exact Submodule.add_mem_sup h1 h2

private theorem exists_inv {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.Projective A M] (g : M →ₗ[A] M) (J : Ideal A)
    (h : LinearMap.range g ⊔ (J • ⊤ : Submodule A M) = ⊤) :
    ∃ k : M →ₗ[A] M, ∀ x, g (k x) - x ∈ (J • ⊤ : Submodule A M) ∧ k (g x) - x ∈ (J • ⊤ : Submodule A M) := by
  set P : Submodule A M := J • ⊤ with hP
  have hs : Function.Surjective (P.mkQ ∘ₗ g) := by
    intro y
    obtain ⟨x, rfl⟩ := P.mkQ_surjective y
    have hx : x ∈ LinearMap.range g ⊔ P := by rw [h]; trivial
    obtain ⟨r, ⟨a, rfl⟩, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    refine ⟨a, ?_⟩
    simp [(Submodule.Quotient.mk_eq_zero P).2 hz]
  obtain ⟨k, hk⟩ := Module.projective_lifting_property (P.mkQ ∘ₗ g) P.mkQ hs
  have hk' : ∀ x, P.mkQ (g (k x)) = P.mkQ x := fun x => LinearMap.congr_fun hk x
  have hle : P ≤ P.comap g := by
    intro x hx
    have h1 := Submodule.mem_map_of_mem (f := g) hx
    rw [hP, Submodule.map_smul''] at h1
    exact Submodule.smul_mono le_rfl le_top h1
  let gb : (M ⧸ P) →ₗ[A] (M ⧸ P) := P.mapQ P g hle
  have hgb : ∀ x, gb (P.mkQ x) = P.mkQ (g x) := fun x => rfl
  have hsb : Function.Surjective gb := by
    intro y
    obtain ⟨z, hz⟩ := hs y
    exact ⟨P.mkQ z, by rw [hgb]; exact hz⟩
  have hib : Function.Injective gb := OrzechProperty.injective_of_surjective_endomorphism gb hsb
  refine ⟨k, fun x => ⟨?_, ?_⟩⟩
  · exact (Submodule.Quotient.eq P).1 (hk' x)
  · refine (Submodule.Quotient.eq P).1 (hib ?_)
    change gb (P.mkQ _) = gb (P.mkQ _)
    rw [hgb, hgb, hk']

end UpperTheory.Gal.FiniteEtaleModels.O.LU

open UpperTheory.Gal.FiniteEtaleModels.O.LU in
theorem UpperTheory.Gal.FiniteEtaleModels.O.liftUnit :
    UpperTheory.Gal.FiniteEtaleModels.O.LiftUnit := by
  intro A M _ _ _ _ _ _ u 𝔞 hu _
  set N : Submodule A M := 𝔞 • ⊤ with hN
  intro g₀
  obtain ⟨g', hg'⟩ := Module.projective_lifting_property N.mkQ (g₀.toLinearMap ∘ₗ N.mkQ) N.mkQ_surjective
  obtain ⟨s, t, hs, hst, ht⟩ := exists_sep u 𝔞 hu
  let g : M →ₗ[A] M := t • g' + s • LinearMap.id
  have hgv : ∀ x, g x = t • g' x + s • x := fun x => rfl
  have ht1 : t = 1 - s := by rw [← hst]; ring
  have hs1 : s = 1 - t := by rw [← hst]; ring
  have hgg' : ∀ x, g x - g' x ∈ N := fun x => by
    have h1 : g x - g' x = s • (x - g' x) := by
      rw [hgv, ht1, sub_smul, one_smul, smul_sub]; abel
    rw [h1]
    exact Submodule.smul_mem_smul hs trivial
  have hlift : ∀ x, N.mkQ (g x) = g₀ (N.mkQ x) := fun x => by
    have h1 : N.mkQ (g x) = N.mkQ (g' x) := (Submodule.Quotient.eq N).2 (hgg' x)
    rw [h1]
    exact LinearMap.congr_fun hg' x
  have hmax : ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → u ≤ 𝔪 →
      LinearMap.range g ⊔ (𝔪 • ⊤ : Submodule A M) = ⊤ := by
    intro 𝔪 hm hum
    rw [eq_top_iff]
    intro x _
    by_cases ha : 𝔞 ≤ 𝔪
    · obtain ⟨y, hy⟩ := g₀.surjective (N.mkQ x)
      obtain ⟨y, rfl⟩ := N.mkQ_surjective y
      have h1 : x - g y ∈ N := (Submodule.Quotient.eq N).1 (show N.mkQ x = N.mkQ (g y) by rw [hlift, hy])
      have h2 : x - g y ∈ (𝔪 • ⊤ : Submodule A M) := Submodule.smul_mono_left ha h1
      have h3 := Submodule.add_mem_sup (LinearMap.mem_range_self g y) h2
      simpa using h3
    · have htm := ht 𝔪 hm hum ha
      have h1 : x - g x = t • (x - g' x) := by
        rw [hgv, hs1, sub_smul, one_smul, smul_sub]; abel
      have h2 : x - g x ∈ (𝔪 • ⊤ : Submodule A M) := by
        rw [h1]
        exact Submodule.smul_mem_smul htm trivial
      have h3 := Submodule.add_mem_sup (LinearMap.mem_range_self g x) h2
      simpa using h3
  choose h hh using fun e => exists_inv g (u ^ e) (sup_range_pow g u hmax e)
  exact ⟨g, h, hlift, fun e x => hh e x⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.StepBOf
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.crystallineComparison.Mod (Std TjD KerAt)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.stepB_of :
    TjExG → BRead → BKer → BLev → DescExt → BaseFet → BaseOnto → UpperTheory.Gal.crystallineComparison.Mod.PulledEx → StepB := by
  intro hTj hRead hKer hLev hDesc hFet hOnto hPul p _ D G L sc E _ _ gb w q _ r 𝔴 𝔫 S k T N₀ 𝔟₁ 𝔟₂ X₁ X₂ 𝔴' i hmax hu hb hi h hint htj
    M₁ M₂ c₁ c₂ a₁ a₂ n₁ n₂ _ C₁ C₂ W
  have hq : q.Prime := Fact.out
  obtain ⟨f, ⟨hf, ⟨mf⟩⟩, -⟩ := X₂.M.rep _ _ X₁.Y.univ
  have hqw : (q : 𝓞 D.F) ∈ 𝔴' := hu (Ideal.subset_span (Set.mem_insert _ _))
  have hd : Ideal.absNorm 𝔴' ∣ q ^ Module.finrank ℤ (𝓞 D.F) := by
    have := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem 𝔴').2 hqw)
    rwa [Ideal.absNorm_span_natCast] at this
  obtain ⟨f', -, hf'⟩ := (Nat.dvd_prime_pow hq).1 hd
  have hpos : 0 < f' := Nat.pos_of_ne_zero fun h0 => hmax.ne_top (Ideal.absNorm_eq_one_iff.1 (by simpa [h0] using hf'))
  have he : Ideal.absNorm 𝔴' ^ i = q ^ (f' * i) := by rw [hf', pow_mul]
  have he' : 0 < i → 0 < f' * i := fun h => Nat.mul_pos hpos h
  obtain ⟨Tj⟩ := hTj q (datAt S.atq S.sp) (Ow w) S.b N₀ X₂.lev.1 X₂.lev.2.1 S.std.pmem S.std.m1 r 𝔴' i (f' * i) hmax hu hi he' X₂.M
  obtain ⟨B⟩ := hRead p D G L sc E gb w q r 𝔴 𝔫 S k T N₀ 𝔟₁ 𝔟₂ X₁ X₂ 𝔴' i hmax hu hb hi h hint htj M₁ M₂ c₁ c₂ a₁ a₂ n₁ n₂ C₁ C₂ W f mf hf
    _ he he' Tj
  have k1 := hKer p D G L sc E gb w q r 𝔴 𝔫 S k T N₀ 𝔟₁ 𝔟₂ X₁ X₂ 𝔴' i hmax hu hb hi h hint htj M₁ M₂ c₁ c₂ a₁ a₂ n₁ n₂ C₁ C₂ W f mf hf
    _ he he' Tj B
  have k2 := hLev p D G L sc E gb w q r 𝔴 𝔫 S k T N₀ 𝔟₁ 𝔟₂ X₁ X₂ 𝔴' i hmax hu hb hi h hint htj M₁ M₂ c₁ c₂ a₁ a₂ n₁ n₂ C₁ C₂ W f mf hf
    _ he he' Tj B
  obtain ⟨hfin, het⟩ := hFet p D G L sc E gb w q r 𝔴 _ X₁.site k T M₁ c₁ a₁ n₁ C₁
  have honto := hOnto p D G L sc E gb w q r 𝔴 _ X₁.site k T M₁ c₁ a₁ n₁ C₁
  have hsm : Smooth X₁.Y.s := by
    haveI := X₁.M.smooth
    haveI : Smooth X₁.M.s := SmoothOfRelativeDimension.smooth (D.a * (D.n - 1)) X₁.M.s
    haveI := X₁.et
    rw [← X₁.ov]
    infer_instance
  obtain ⟨y', hy, hys⟩ := hDesc (Ow w) E _ _ _ _ X₁.Y.s _ C₁.j C₁.ov hsm hfin het honto f Tj.s B.y Tj.fin B.ys k1
  obtain ⟨P⟩ := hPul q (datAt S.atq S.sp) (Ow w) S.b N₀ X₂.lev.1 X₂.lev.2.1 X₂.M r 𝔴' i _ Tj _ f _ hf X₁.Y.univ mf y' hys
  obtain ⟨t, ht, htπ⟩ := hDesc (Ow w) E _ _ _ _ X₁.Y.s _ C₁.j C₁.ov hsm hfin het honto (y' ≫ Tj.t) X₂.π (W.π ≫ C₂.j) X₂.fin
    (by rw [← Category.assoc C₁.j, hy, B.yt, Category.assoc]) fun Ω _ _ x x' e => k2 Ω x x' e (k1 Ω x x' e)
  have hw : (P.ψ.left ≫ P.m'.φ ≫ Tj.mt.φ) ≫ X₂.M.univ.A.hom = (X₁.Y.univ.A.hom ≫ t) ≫ X₂.π := by
    rw [Category.assoc, Category.assoc, Tj.mt.cart.1.w, ← Category.assoc P.m'.φ, P.m'.cart.1.w, Category.assoc, ← Category.assoc,
      Over.w P.ψ, Category.assoc, htπ]
  have hfa : C₁.m.φ ≫ P.m₀.φ = B.fa := Tj.ms.cart.1.hom_ext
    (by rw [Category.assoc, P.tri, B.ms])
    (by rw [Category.assoc, P.m₀.cart.1.w, ← Category.assoc, C₁.m.cart.1.w, Category.assoc, hy, B.ca.1.w])
  refine ⟨⟨t, ?_, X₂.mπ.cart.1.lift _ _ hw, X₂.mπ.cart.1.lift_snd _ _ _⟩, ht, X₂.mπ.cart.1.hom_ext ?_ ?_⟩
  · rw [← X₂.ov, ← Category.assoc, htπ, Category.assoc, ← Tj.st, ← Category.assoc, hys, hf]
  · rw [Category.assoc, IsPullback.lift_fst, ← Category.assoc P.ψ.left, ← P.sq, Category.assoc, ← Category.assoc, hfa,
      ← Category.assoc, B.sq, Category.assoc, B.mt]
    simp only [Category.assoc]
  · rw [Category.assoc, IsPullback.lift_snd, ← Category.assoc, C₁.m.cart.1.w, Category.assoc, ht]
    simp only [Category.assoc]
    rw [C₂.m.cart.1.w, ← Category.assoc W.φ.φ, W.φ.cart.1.w, Category.assoc, ← Category.assoc W.ψ.left, Over.w W.ψ]
end


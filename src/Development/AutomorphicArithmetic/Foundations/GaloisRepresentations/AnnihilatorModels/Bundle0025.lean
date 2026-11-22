import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0001
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3164
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0402

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MTjEEx
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.tjEEx_of :
    ObjTri → PulledEx → PullKer → UKerW → LevPull → LevPush → TjEEx := by
  intro hTri hPE hPK hUW hLP hLPush p _ D O _ _ _ _ f b N r w _ hS M j c T hF 𝔞 ρ hsup hu E π hπ mπ
  have h3 := hS.three
  have hcop := hS.cop
  obtain ⟨Z, s, g, pb⟩ : ∃ (Z : Scheme.{0}) (s : Z ⟶ E.X) (g : Z ⟶ T.Y), IsPullback s g π T.s :=
    ⟨_, _, _, IsPullback.of_hasPullback π T.s⟩
  obtain ⟨o, ⟨ms⟩⟩ := GlobalTheory.T.exists_harrisTaylorObject_pullback p D O b N E.X Z E.s s E.univ
  obtain ⟨m₁, hm₁⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ ms mπ
  have hx : (s ≫ π) ≫ M.s = s ≫ E.s := by rw [Category.assoc, hπ]
  obtain ⟨P⟩ := hPE p D O b N h3 hcop M r w j c T Z (s ≫ π) (s ≫ E.s) hx o m₁ g pb.w.symm
  obtain ⟨l, hl, hlm⟩ := hLP p D O b N E.X Z E.s (s ≫ E.s) s E.univ o ms 𝔞 ρ E.lv E.isLev
  have hK : ∀ (X : Over Z) (g' : X ⟶ o.A), UKer r o P.ψ X g' → KilledBy o w g' := by
    rintro X g' ⟨h1, e, h2⟩
    let g₀ : (Over.mk (X.hom ≫ g) : Over T.Y) ⟶ T.o.A := Over.homMk (g'.left ≫ P.m₀.φ) (by
      have hw := P.m₀.cart.1.w
      have hg := Over.w g'
      simp only [Category.assoc, hw, Over.mk_hom]
      rw [← Category.assoc, hg])
    obtain ⟨Ha, -, Hc⟩ := (hPK p D O b N T.Y Z (T.s ≫ M.s) (s ≫ E.s) g T.o T.o' o P.o' P.m₀ P.m' T.ψ P.ψ P.sq).1
      X (Over.mk (X.hom ≫ g)) rfl g' g₀ (by simp [g₀])
    exact (Hc w).2 (hUW p D O f b N r w hS M j c T hF _ g₀ ⟨Ha.1 h1, e, (Hc _).1 h2⟩)
  have hl' := hLPush p D O b N r w 𝔞 ρ hsup hu Z (s ≫ E.s) c o P.o' P.ψ P.isog hK l hl
  obtain ⟨t, ⟨ht, mt, hlev⟩, -⟩ := E.rep Z (s ≫ E.s) P.o' _ hl'
  obtain ⟨n₁, hn₁⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ mt mπ
  obtain ⟨n₂, hn₂⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ P.m' T.mt
  have e : t ≫ π = g ≫ T.t := (M.rep Z (s ≫ E.s) P.o').unique
    ⟨by rw [Category.assoc, hπ, ht], ⟨n₁⟩⟩
    ⟨by rw [Category.assoc, ← T.st, ← Category.assoc, ← pb.w, Category.assoc, hπ], ⟨n₂⟩⟩
  have hφ : ∀ (f₁ f₂ : Z ⟶ M.X) (_ : f₁ = f₂) (a : ObjMap P.o' M.univ f₁) (a' : ObjMap P.o' M.univ f₂), a.φ = a'.φ := by
    rintro f₁ _ rfl a a'
    exact (hTri p D O b N h3 hcop Z M.X M.X _ M.s M.s P.o' M.univ M.univ f₁ (𝟙 _)).1 a a'
  refine ⟨{ Z := Z, s := s, t := t, g := g, pb := pb, tπ := e, o := o, o' := P.o', ms := ms, mt := mt, ψ := P.ψ,
            isog := P.isog, tj := P.tj, m₀ := P.m₀, m' := P.m', sq := P.sq, tri := P.tri.trans hm₁,
            tri' := hn₂.symm.trans ((hφ _ _ e.symm n₂ n₁).trans hn₁), lev := ?_ }⟩
  intro y l' hl''
  have hll : l' = l y := by
    apply Over.OverMorphism.ext
    apply ms.cart.1.hom_ext
    · rw [hl'', hlm]
    · rw [Over.w l', Over.w (l y)]
  subst hll
  exact hlev y
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MTjExF
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private theorem isUnit_natCast_of {X Y : Scheme.{0}} (g : X ⟶ Y) {n : ℕ} (h : IsUnit ((n : ℕ) : Γ(Y, ⊤))) :
    IsUnit ((n : ℕ) : Γ(X, ⊤)) := by
  have := h.map g.appTop.hom
  rwa [map_natCast] at this

private theorem exists_id {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    (hT : ObjTri) (hN : 3 ≤ N) (hNp : N.Coprime p) {S S₃ : Scheme.{0}} {s : S ⟶ Sp R} {s₃ : S₃ ⟶ Sp R}
    {o : Obj b N s} {o₃ : Obj b N s₃} {g : S ⟶ S₃} (m : ObjMap o o₃ g) :
    ∃ i : ObjMap o o (𝟙 S), i.φ = 𝟙 _ := by
  obtain ⟨i, hi⟩ := (hT p D R b N hN hNp _ _ _ _ _ _ o o o₃ (𝟙 S) g).2 g (Category.id_comp g) m m
  refine ⟨i, m.cart.1.hom_ext ?_ ?_⟩
  · rw [hi, Category.id_comp]
  · rw [i.cart.1.w, Category.comp_id, Category.id_comp]

private theorem et_of {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    (hT : ObjTri) (hI : PullIsog) (hK : PullKer) (hN : 3 ≤ N) (hNp : N.Coprime p)
    {M : Model b N} {r : ℤ} {w : Ideal (𝓞 D.F)} {j c : ℕ}
    {Y : Scheme.{0}} {s : Y ⟶ M.X} {o o' : Obj b N (s ≫ M.s)} (ms : ObjMap o M.univ s) {ψ : o.A ⟶ o'.A}
    (iso : IsPIsog c o o' ψ) (tj : IsTj r w j o o' ψ) (hY : Univ r w j c M s o o' ψ)
    {Y₀ : Scheme.{0}} {s₀ : Y₀ ⟶ M.X} (gs : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme)
    (hgs : gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀) (egs : Etale gs)
    {o₀ o₀' : Obj b N (s₀ ≫ M.s)} (ms₀ : ObjMap o₀ M.univ s₀) {ψ₀ : o₀.A ⟶ o₀'.A}
    (iso₀ : IsPIsog c o₀ o₀' ψ₀) (tj₀ : IsTj r w j o₀ o₀' ψ₀) (hY₀ : Univ r w j c M s₀ o₀ o₀' ψ₀) :
    Etale (s ∣_ M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))) := by
  have hpU : IsUnit ((p : ℕ) : Γ((M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme, ⊤)) := by
    have h0 := GlobalTheory.EtC.PairDich.isUnit_ι_appTop (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))) ((p : ℕ) : Γ(M.X, ⊤)) le_rfl
    rwa [map_natCast] at h0
  have hp₀ : IsUnit ((p : ℕ) : Γ(Y₀, ⊤)) := isUnit_natCast_of gs hpU
  have hpV : IsUnit ((p : ℕ) : Γ((s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).toScheme, ⊤)) :=
    isUnit_natCast_of (s ∣_ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))) hpU
  have hPB := isPullback_morphismRestrict s (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))
  obtain ⟨oV, ⟨mV⟩⟩ := GlobalTheory.T.exists_harrisTaylorObject_pullback p D R b N M.X (s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).toScheme M.s
    ((s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).ι ≫ s) M.univ
  obtain ⟨mVo, -⟩ := (hT p D R b N hN hNp _ Y M.X _ (s ≫ M.s) M.s oV o M.univ
    (s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).ι s).2 _ rfl mV ms
  obtain ⟨oV', mV', ψV, isoV, sqV⟩ := hI p D R b N Y (s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).toScheme
    (s ≫ M.s) _ (s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).ι (Category.assoc _ _ _).symm c o o' ψ iso oV mVo
  have tjV := (hK p D R b N Y _ (s ≫ M.s) _ (s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).ι
    o o' oV oV' mVo mV' ψ ψV sqV).2 r w j tj
  obtain ⟨y₀, ⟨hy₀, m₀y, m₁y, hsq₀⟩, -⟩ := hY Y₀ s₀ o₀ o₀' ms₀ ψ₀ hp₀ iso₀ tj₀
  obtain ⟨v, ⟨hv, m₀v, m₁v, hsqv⟩, -⟩ :=
    hY₀ _ ((s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).ι ≫ s) oV oV' mV ψV hpV isoV tjV
  have hvy : v ≫ y₀ = (s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).ι := by
    apply (hY _ ((s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).ι ≫ s) oV oV' mV ψV hpV isoV tjV).unique
    · refine ⟨by rw [Category.assoc, hy₀, hv], ?_⟩
      obtain ⟨a, ha⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m₀v m₀y
      obtain ⟨a', ha'⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m₁v m₁y
      refine ⟨a, a', ?_⟩
      rw [ha, ha', Category.assoc m₀v.φ m₀y.φ, hsq₀, ← Category.assoc m₀v.φ, hsqv,
        Category.assoc (Over.Hom.left ψV) m₁v.φ m₁y.φ]
    · exact ⟨rfl, mVo, mV', sqV⟩
  let u : Y₀ ⟶ (s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).toScheme := hPB.lift gs y₀ (by rw [hgs, hy₀])
  have hu₁ : u ≫ s ∣_ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))) = gs := hPB.lift_fst _ _ _
  have hu₂ : u ≫ (s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).ι = y₀ := hPB.lift_snd _ _ _
  have hvg : v ≫ gs = s ∣_ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))) := by
    rw [← cancel_mono (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι, Category.assoc, hgs, hv, morphismRestrict_ι]
  have hvu : v ≫ u = 𝟙 _ := by
    apply hPB.hom_ext
    · rw [Category.assoc, hu₁, hvg, Category.id_comp]
    · rw [Category.assoc, hu₂, hvy, Category.id_comp]
  have huv : u ≫ v = 𝟙 Y₀ := by
    apply (hY₀ Y₀ s₀ o₀ o₀' ms₀ ψ₀ hp₀ iso₀ tj₀).unique
    · refine ⟨by rw [Category.assoc, hv, ← Category.assoc, hu₂, hy₀], ?_⟩
      have hc : (u ≫ v) ≫ y₀ = y₀ := by rw [Category.assoc, hvy, hu₂]
      obtain ⟨a, ha⟩ := (hT p D R b N hN hNp Y₀ Y₀ Y _ _ _ o₀ o₀ o (u ≫ v) y₀).2 y₀ hc m₀y m₀y
      obtain ⟨a', ha'⟩ := (hT p D R b N hN hNp Y₀ Y₀ Y _ _ _ o₀' o₀' o' (u ≫ v) y₀).2 y₀ hc m₁y m₁y
      refine ⟨a, a', ?_⟩
      apply m₁y.cart.1.hom_ext
      · rw [Category.assoc a.φ, ← hsq₀, ← Category.assoc a.φ, ha, hsq₀, Category.assoc (Over.Hom.left ψ₀) a'.φ, ha']
      · have e1 := a.cart.1.w
        have e2 := a'.cart.1.w
        calc (a.φ ≫ Over.Hom.left ψ₀) ≫ o₀'.A.hom = a.φ ≫ o₀.A.hom := by rw [Category.assoc a.φ, Over.w]
          _ = o₀.A.hom ≫ (u ≫ v) := e1
          _ = (Over.Hom.left ψ₀ ≫ o₀'.A.hom) ≫ (u ≫ v) := by rw [Over.w]
          _ = (Over.Hom.left ψ₀ ≫ a'.φ) ≫ o₀'.A.hom := by
            rw [Category.assoc (Over.Hom.left ψ₀) o₀'.A.hom, ← e2, Category.assoc (Over.Hom.left ψ₀) a'.φ]
    · refine ⟨Category.id_comp _, ?_⟩
      obtain ⟨i, hi⟩ := exists_id hT hN hNp ms₀
      obtain ⟨i', hi'⟩ := exists_id hT hN hNp m₁y
      exact ⟨i, i', by rw [hi, hi', Category.id_comp, Category.comp_id]⟩
  haveI : IsIso v := ⟨⟨u, hvu, huv⟩⟩
  rw [← hvg]
  infer_instance

theorem UpperTheory.Gal.crystallineComparison.Mod.tjExF_of :
    EsNorm → EsGen → ObjTri → PullIsog → PullKer → TjExF := by
  intro hE hG hT hI hK p _ D O _ _ _ _ f b N r w _ hS M j hj
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · have h1 := hS.norm
      rw [pow_zero, Ideal.absNorm_eq_one_iff] at h1
      exact absurd h1 (Ideal.IsMaximal.ne_top inferInstance)
    · exact h
  have hc : ∃ e : ℕ, p ^ (f * j) = p ^ e ∧ (0 < j → 0 < e) :=
    ⟨f * j, rfl, fun h => Nat.mul_pos hf h⟩
  obtain ⟨Y, s, t, o, o', ms, mt, ψ, st, fin, -, -, flat, iso, tj, univ⟩ :=
    hE p D O b N hS.three hS.cop hS.pmem r w j (p ^ (f * j)) inferInstance hS.ule hj hc hS.m1 M
  obtain ⟨Y₀, s₀, t₀, gs, gt, o₀, o₀', ms₀, mt₀, ψ₀, -, hgs, -, -, egs, -, -, iso₀, tj₀, univ₀⟩ :=
    hG p D O b N hS.three hS.cop hS.pmem r w j (p ^ (f * j)) inferInstance hS.ule hj hc hS.m1 M
  exact ⟨⟨Y, s, t, st, o, o', ms, mt, ψ, fin,
    et_of hT hI hK hS.three hS.cop ms iso tj univ gs hgs egs ms₀ iso₀ tj₀ univ₀, iso, tj, univ⟩, flat⟩
end


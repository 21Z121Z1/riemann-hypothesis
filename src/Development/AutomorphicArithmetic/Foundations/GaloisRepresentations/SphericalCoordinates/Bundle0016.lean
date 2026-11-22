import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PSumPts
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem finsum_sigma {I : Type} {κ : I → Type} (f : (Σ i, κ i) → ℂ)
    (hf : (Function.support f).Finite) : ∑ᶠ s, f s = ∑ᶠ i, ∑ᶠ k, f ⟨i, k⟩ := by
  classical
  have hfi : ∀ i, (Function.support (fun k : κ i => f ⟨i, k⟩)).Finite := fun i =>
    hf.preimage (fun a _ b _ h => sigma_mk_injective h)
  rw [finsum_eq_sum_of_support_subset f (s := hf.toFinset) (by simp)]
  have hg : Function.support (fun i => ∑ᶠ k, f ⟨i, k⟩) ⊆ ↑(hf.toFinset.image Sigma.fst) := by
    intro i hi
    obtain ⟨k, hk⟩ : ∃ k, f ⟨i, k⟩ ≠ 0 := by
      by_contra h
      push_neg at h
      exact hi (finsum_eq_zero_of_forall_eq_zero h)
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
    exact ⟨⟨i, k⟩, by simpa using hk, rfl⟩
  rw [finsum_eq_sum_of_support_subset _ hg]
  have hk : ∀ i, ∑ᶠ k, f ⟨i, k⟩ = ∑ k ∈ (hfi i).toFinset, f ⟨i, k⟩ := fun i =>
    finsum_eq_sum_of_support_subset _ (by simp)
  simp_rw [hk]
  rw [← Finset.sum_sigma]
  apply Finset.sum_congr ?_ (fun _ _ => rfl)
  ext ⟨i, k⟩
  simp only [Set.Finite.mem_toFinset, Function.mem_support, Finset.mem_sigma, Finset.mem_image]
  constructor
  · intro h
    exact ⟨⟨⟨i, k⟩, h, rfl⟩, h⟩
  · rintro ⟨-, h⟩
    exact h

private noncomputable def tm {p : ℕ} [Fact p.Prime] {G : HTGroup p} (v : InfinitePlace G.F) (c : G.F[X] → ℂ → ℂ)
    (K : Subgroup G.GAf) (S : Set G.GAf) (B : GlobalTheory.LKCx.Form G) (b : GlobalTheory.LKCx.Dat G v B.β) : ℂ :=
  ((Nat.card (GlobalTheory.LKCx.Form.Stab v B K (KHT p G.m G.n 1 G.Fw) b) : ℕ) : ℂ)⁻¹ *
    ∑ᶠ y : GlobalTheory.LKCx.grp G B.β, if GlobalTheory.LKCx.FixL G v B.β y b.2.1 then
      (S.indicator (1 : G.GAf → ℂ)) (b.1.1⁻¹ * B.toAf y * b.1.1) *
        (((KHT p G.m G.n 1 G.Fw) : Set (Gr G 1)).indicator (1 : Gr G 1 → ℂ))
          (b.1.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β y * b.1.2) *
        c (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) (GlobalTheory.RootSumWeights.eigL G v B.β y b.2.1) else 0

private theorem tm_eq {p : ℕ} [Fact p.Prime] {G : HTGroup p} (v : InfinitePlace G.F) (c : G.F[X] → ℂ → ℂ)
    (K : Subgroup G.GAf) (S : Set G.GAf) (B : GlobalTheory.LKCx.Form G) (b : GlobalTheory.LKCx.Dat G v B.β)
    (hK : ∀ y, Sees B (K : Set G.GAf) b y → y = 1) :
    tm v c K S B b = ∑ᶠ y : GlobalTheory.LKCx.grp G B.β, if Sees B S b y then
      c (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) (GlobalTheory.RootSumWeights.eigL G v B.β y b.2.1) else 0 := by
  have hcard : Nat.card (GlobalTheory.LKCx.Form.Stab v B K (KHT p G.m G.n 1 G.Fw) b) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun s t => ?_⟩, ⟨LKCx.Stab.one G v B.β _ _ _ K _ b⟩⟩
    obtain ⟨y, hy1, hy2, hy3⟩ := s
    obtain ⟨y', hy1', hy2', hy3'⟩ := t
    have e1 : y = 1 := hK y ⟨hy3, hy1, hy2⟩
    have e2 : y' = 1 := hK y' ⟨hy3', hy1', hy2'⟩
    subst e1
    subst e2
    rfl
  unfold tm
  rw [hcard, Nat.cast_one, inv_one, _root_.one_mul]
  apply finsum_congr
  intro y
  unfold Sees
  by_cases hF : GlobalTheory.LKCx.FixL G v B.β y b.2.1
  · by_cases h1 : b.1.1⁻¹ * B.toAf y * b.1.1 ∈ S
    · by_cases h2 : b.1.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β y * b.1.2 ∈ KHT p G.m G.n 1 G.Fw
      · simp [hF, h1, h2]
      · simp [hF, h1, h2]
    · simp [hF, h1]
  · simp [hF]

theorem UpperTheory.Gal.W2.sumPts_of :
    UpperTheory.Gal.W2.EigSame → UpperTheory.Gal.W2.SumPts := by
  intro hE p _ G v c K S hconj hK hS T Φ Fb w hx
  classical
  let g : LKCx.AllPts G v K (KHT p G.m G.n 1 G.Fw) → ℂ := fun s => tm v c K S (Quot.out s.1) (Quot.out s.2)
  have key : ∀ x : T, g (Φ x) = if x ∈ Fb then w x else 0 := by
    intro x
    obtain ⟨q, a, hΦ, hFb, hw⟩ := hx x
    obtain ⟨pt, hpt⟩ : ∃ pt : LKCx.Form.Pts v (Quot.out q) K (KHT p G.m G.n 1 G.Fw), Quot.mk _ a = pt := ⟨_, rfl⟩
    rw [hpt] at hΦ
    have hmk : Quot.mk _ a = Quot.mk _ (Quot.out pt) := hpt.trans (Quot.out_eq pt).symm
    obtain ⟨E, -, hE1⟩ := hE p G v c (Quot.out q) K S hconj a (Quot.out pt) hmk
    obtain ⟨E', -, hE2⟩ := hE p G v c (Quot.out q) K S hconj (Quot.out pt) a hmk.symm
    have hg : g (Φ x) = g ⟨q, pt⟩ := by rw [hΦ]
    rw [hg]
    show tm v c K S (Quot.out q) (Quot.out pt) = _
    rw [tm_eq v c K S _ _ (hK _ _)]
    by_cases hxF : x ∈ Fb
    · rw [if_pos hxF]
      obtain ⟨y, hy⟩ := hFb.1 hxF
      have hy' := ((hE1 y).1).1 hy
      rw [finsum_eq_single _ (E y)]
      · rw [if_pos hy', ((hE1 y).2 hy).1, ((hE1 y).2 hy).2, hw y hy]
      · intro y' hne
        rw [if_neg]
        intro hs
        exact hne (hS _ _ _ _ hs hy')
    · rw [if_neg hxF]
      apply finsum_eq_zero_of_forall_eq_zero
      intro y'
      rw [if_neg]
      intro hs
      exact hxF (hFb.2 ⟨E' y', ((hE2 y').1).1 hs⟩)
  have hsupp : Function.support (fun x => g (Φ x)) ⊆ ↑Fb := by
    intro x hx0
    by_contra hn
    exact hx0 (by show g (Φ x) = 0; rw [key x, if_neg (show x ∉ Fb from hn)])
  have hfin : (Function.support g).Finite := by
    apply ((Fb.finite_toSet).image Φ).subset
    intro s hs
    refine ⟨Φ.symm s, hsupp ?_, Φ.apply_symm_apply s⟩
    show g (Φ (Φ.symm s)) ≠ 0
    rw [Φ.apply_symm_apply]
    exact hs
  have h1 : RootSumWeights.cxTotalM G v c K (S.indicator 1) (KHT p G.m G.n 1 G.Fw)
      ((↑(KHT p G.m G.n 1 G.Fw) : Set (Gr G 1)).indicator 1) = ∑ᶠ s, g s := by
    rw [finsum_sigma g hfin]
    rfl
  rw [h1, ← finsum_comp_equiv Φ, finsum_eq_sum_of_support_subset (fun x => g (Φ x)) hsupp]
  exact Finset.sum_congr rfl (fun x hx => by rw [key, if_pos hx])
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PUnifG
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem u_eq_of_marked {O : Type} [Ring O] {bar : O → O} {g : ℕ} {ρ : O →+* Matrix (Fin g) (Fin g) ℂ}
    {Λ : Type} {F : Fam ℂ O Λ g} {N : ℕ} {Cl : ∀ D' : PLat O bar, (Λ → D'.La) → Prop}
    (U : Unif F (RingHom.id ℂ) ρ N Cl) (i i' : Fin U.n) (P : (U.Di i).La →+ (Fin g → ℂ))
    (P' : (U.Di i').La →+ (Fin g → ℂ)) (hP : IsPeriod (U.Di i) ρ P) (hP' : IsPeriod (U.Di i') ρ P')
    (w : (U.Di i').La ≃ₗ[O] (U.Di i).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
    (hw : IsMarkedIsom N (U.Di i') (U.Di i) (U.t i') (U.t i) w) (hh : ∀ u, P (w u) = h (P' u)) :
    U.u i' P' = U.u i P := by
  obtain rfl := U.distinct i' i w hw
  exact (U.fibre i' P' P hP' hP).2 ⟨w, h, hw, hh⟩

private theorem marked_of_u_eq {O : Type} [Ring O] {bar : O → O} {g : ℕ} {ρ : O →+* Matrix (Fin g) (Fin g) ℂ}
    {Λ : Type} {F : Fam ℂ O Λ g} {N : ℕ} {Cl : ∀ D' : PLat O bar, (Λ → D'.La) → Prop}
    (U : Unif F (RingHom.id ℂ) ρ N Cl) (i i' : Fin U.n) (P : (U.Di i).La →+ (Fin g → ℂ))
    (P' : (U.Di i').La →+ (Fin g → ℂ)) (hP : IsPeriod (U.Di i) ρ P) (hP' : IsPeriod (U.Di i') ρ P')
    (e : U.u i' P' = U.u i P) :
    ∃ (w : (U.Di i').La ≃ₗ[O] (U.Di i).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
      IsMarkedIsom N (U.Di i') (U.Di i) (U.t i') (U.t i) w ∧ ∀ u, P (w u) = h (P' u) := by
  obtain rfl := U.disj i' i P' P hP' hP e
  exact (U.fibre i' P' P hP' hP).1 e

private theorem isPeriod_comp {O : Type} [Ring O] {bar : O → O} {g : ℕ} {ρ : O →+* Matrix (Fin g) (Fin g) ℂ}
    {D' D'' : PLat O bar} {P : D'.La →+ (Fin g → ℂ)} (hP : IsPeriod D' ρ P) (w : D''.La ≃ₗ[O] D'.La)
    (hw : IsIsom D'' D' w) : IsPeriod D'' ρ (P.comp w.toLinearMap.toAddMonoidHom) := by
  obtain ⟨h1, h2, h3, h4, Hm, hH, hpos, hEF⟩ := hP
  have hs : Set.range (P.comp w.toLinearMap.toAddMonoidHom) = Set.range P := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨w x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨w.symm x, by simp⟩
  have hr : (P.comp w.toLinearMap.toAddMonoidHom).range = P.range := by
    ext z
    exact Set.ext_iff.1 hs z
  refine ⟨fun a x => ?_, h2.comp w.injective, ?_, ?_, Hm, hH, hpos, fun x y => ?_⟩
  · show P (w (a • x)) = _
    rw [map_smul, h1]
    rfl
  · rw [hr]
    exact h3
  · rw [hs]
    exact h4
  · show (hermForm Hm (P (w x)) (P (w y))).im = _
    rw [hEF, hw x y]

private theorem marked_symm {O : Type} [Ring O] {bar : O → O} {Λ : Type} {N : ℕ} {D₁ D₂ : PLat O bar}
    {t₁ : Λ → D₁.La} {t₂ : Λ → D₂.La} {w : D₁.La ≃ₗ[O] D₂.La} (h : IsMarkedIsom N D₁ D₂ t₁ t₂ w) :
    IsMarkedIsom N D₂ D₁ t₂ t₁ w.symm := by
  refine ⟨fun x y => ?_, fun a => ?_⟩
  · have := h.1 (w.symm x) (w.symm y)
    simpa using this.symm
  · obtain ⟨e, he⟩ := h.2 a
    refine ⟨-(w.symm e), ?_⟩
    have h2 := congrArg w.symm he
    rw [LinearEquiv.symm_apply_apply, map_add, map_nsmul] at h2
    rw [h2, smul_neg]
    abel

theorem UpperTheory.Gal.W2.unifG_of :
    UpperTheory.Gal.W2.CoordEx → UpperTheory.Gal.W2.CoordOcc → UpperTheory.Gal.W2.CoordIso → UpperTheory.Gal.W2.CoordMove → UpperTheory.Gal.W2.UnifG := by
  intro hEx hOcc hIso hMove p _ D G L hDa hDm v hv t₀ ht₀ ρ hρ PD RD N hN hNp F U
  have hch : ∀ x : CxPts F.s (RingHom.id ℂ), ∃ (i : Fin U.n) (P : (U.Di i).La →+ (Fin D.g → ℂ))
      (q : GlobalTheory.LKCx.FCls G) (a : GlobalTheory.LKCx.Dat G v (Quot.out q).β) (j : (U.Di i).La →+ VQ D),
      IsPeriod (U.Di i) ρ P ∧ x.1 = U.u i P ∧ IsCoord L (Quot.out q) (PD _) (RD _) N (U.Di i) (U.t i) P j a := by
    intro x
    obtain ⟨i, P, hP, hu⟩ := U.onto x.1 x.2
    obtain ⟨q, a, j, hc⟩ := hEx p D G L hDa hDm v hv t₀ ht₀ ρ hρ PD RD N hN hNp (U.Di i) (U.t i) P (U.mem i) hP
    exact ⟨i, P, q, a, j, hP, hu.symm, hc⟩
  choose i P q a j hP hu hc using hch
  let Φ₀ : CxPts F.s (RingHom.id ℂ) → GlobalTheory.LKCx.AllPts G v (L.KN N) (KHT p G.m G.n 1 G.Fw) :=
    fun x => ⟨q x, Quot.mk _ (a x)⟩
  have hinj : Function.Injective Φ₀ := by
    intro x x' e
    obtain ⟨w, h, hw, hh⟩ := (hIso p D G L v t₀ ρ PD RD N hN hNp (U.Di (i x)) (U.t (i x)) (P x)
      (U.Di (i x')) (U.t (i x')) (P x') (U.mem _) (U.mem _) (q x) (q x') (a x) (a x') (j x) (j x')
      (hc x) (hc x')).2 e
    apply Subtype.ext
    rw [hu x, hu x']
    exact (u_eq_of_marked U _ _ _ _ (hP x) (hP x') w h hw hh).symm
  have hsurj : Function.Surjective Φ₀ := by
    rintro ⟨q₀, c⟩
    obtain ⟨a₀, rfl⟩ := Quot.exists_rep c
    obtain ⟨D', t, Pd, jd, hCl, hPd, hcd⟩ :=
      hOcc p D G L hDa hDm v hv t₀ ht₀ ρ hρ PD RD N hN hNp (Quot.out q₀) a₀
    obtain ⟨i₀, w, hw⟩ := U.all D' t hCl ⟨Pd, hPd⟩
    have hws := marked_symm hw
    let P₀ := Pd.comp w.symm.toLinearMap.toAddMonoidHom
    have hP₀ : IsPeriod (U.Di i₀) ρ P₀ := isPeriod_comp hPd w.symm hws.1
    let j₀ := jd.comp w.symm.toLinearMap.toAddMonoidHom
    have hc₀ : IsCoord L (Quot.out q₀) (PD _) (RD _) N (U.Di i₀) (U.t i₀) P₀ j₀ a₀ :=
      hMove p D G L v t₀ ρ (Quot.out q₀) (PD _) (RD _) N D' t Pd (U.Di i₀) (U.t i₀) P₀ w.symm hws
        (fun _ => rfl) jd j₀ (fun _ => rfl) a₀ hcd
    let x : CxPts F.s (RingHom.id ℂ) := ⟨U.u i₀ P₀, (U.unif i₀ P₀ hP₀).1⟩
    refine ⟨x, ?_⟩
    obtain ⟨w', h', hw', hh'⟩ := marked_of_u_eq U i₀ (i x) P₀ (P x) hP₀ (hP x) (hu x).symm
    exact ((hIso p D G L v t₀ ρ PD RD N hN hNp (U.Di i₀) (U.t i₀) P₀ (U.Di (i x)) (U.t (i x)) (P x)
      (U.mem _) (U.mem _) q₀ (q x) a₀ (a x) j₀ (j x) hc₀ (hc x)).1 ⟨w', h', hw', hh'⟩).symm
  exact ⟨Equiv.ofBijective Φ₀ ⟨hinj, hsurj⟩, fun x => ⟨q x, a x, i x, P x, j x, rfl, hP x, hu x, hc x⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.TotW
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.W2

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {gb : GBase D.toG ℂ}

abbrev TIs {S : Scheme.{0}} {s : S ⟶ Sp ℂ} {N : ℕ} (o : GObj gb N s) {k : Type} [Field k] (t : Sp k ⟶ S) : Type :=
  GTateIso D.toG k (Over.mk t ⟶ o.A) (fun c g => g ≫ o.act.act c)
    (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z))

def IsTr (h : G.GAf) {S : Scheme.{0}} {s : S ⟶ Sp ℂ} {N N' : ℕ} (o' : GObj gb N' s) (o'' : GObj gb N s) (ψ : o'.A ⟶ o''.A) : Prop :=
  IsMonHom ψ ∧ (∀ c : D.O, o'.act.act c ≫ ψ = ψ ≫ o''.act.act c) ∧
    (∃ (ψ' : o''.A ⟶ o'.A) (d : ℕ), IsMonHom ψ' ∧ (∀ c : D.O, o''.act.act c ≫ ψ' = ψ' ≫ o'.act.act c) ∧
      ψ ≫ ψ' = (𝟙 o'.A) ^ d ∧ ψ' ≫ ψ = (𝟙 o''.A) ^ d ∧ d.Coprime p) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S) (β : ℂ →+* k), t ≫ s = spMap β →
      ∃ (I' : TIs o' t) (I'' : TIs o'' t), (∀ y, toUnit _ ≫ o'.eta y = I'.ev N' y) ∧ (∀ y, toUnit _ ≫ o''.eta y = I''.ev N y) ∧
        ∀ n : ℕ, 0 < n → n.Coprime p → ∀ x y : D.La,
          I'.ev n x ≫ ψ = I''.ev n y ↔ ∃ v ∈ LaHat D, L.actG h (inAf D x) = inAf D y + n • v

structure Leg (h : G.GAf) {N N' : ℕ} (X' : GenModel gb N') (X : GenModel gb N) where
  q : X'.X ⟶ X.X
  o : GObj gb N X'.s
  ψ : X'.univ.A ⟶ o.A
  φ : GObjMap o X.univ q
  ov : q ≫ X.s = X'.s
  tr : IsTr L h X'.univ o ψ

variable {L} {h : G.GAf} {N N' : ℕ} {X' : GenModel gb N'} {X : GenModel gb N}

def Leg.tot (c : Leg L h X' X) : X'.univ.A.left ⟶ X.univ.A.left := c.ψ.left ≫ c.φ.φ

theorem Leg.tot_w (c : Leg L h X' X) : c.tot ≫ X.univ.A.hom = X'.univ.A.hom ≫ c.q := by
  rw [Leg.tot, Category.assoc, c.φ.cart.1.w, ← Category.assoc, Over.w]

def Leg.pw (c : Leg L h X' X) (k : ℕ) : (GlobalTheory.KS.pow X'.univ.A k).left ⟶ (GlobalTheory.KS.pow X.univ.A k).left :=
  GlobalTheory.KS.powMap c.q c.tot c.tot_w k

def Leg.tw (c : Leg L h X' X) {k : ℕ} (α : Fin k → 𝓞 D.F) : (GlobalTheory.KS.pow X'.univ.A k).left ⟶ (GlobalTheory.KS.pow X.univ.A k).left :=
  c.pw k ≫ (GlobalTheory.KS.matEnd X.univ.act (Matrix.diagonal fun s => algebraMap (𝓞 D.F) D.O (α s))).left

abbrev sZ {N : ℕ} (X : GenModel gb N) (k : ℕ) : (GlobalTheory.KS.pow X.univ.A k).left ⟶ Sp ℂ := (GlobalTheory.KS.pow X.univ.A k).hom ≫ X.s

def gfamD {N : ℕ} (X : GenModel gb N) (hX : SmoothOfRelativeDimension D.g X.univ.A.hom)
    (hL : (X.univ.P.pull (lift (𝟙 X.univ.A) (𝟙 X.univ.A)).left).IsLB) : Fam ℂ D.O D.La D.g := gfam X.univ hX hL

def LevOk (L : Link D G) (N N' : ℕ) (h : G.GAf) : Prop :=
  3 ≤ N ∧ N.Coprime p ∧ 3 ≤ N' ∧ N'.Coprime p ∧ N ∣ N' ∧ ∀ u ∈ L.KN N', h * u * h⁻¹ ∈ L.KN N

end UpperTheory.Gal.W2
end
end


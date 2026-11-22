import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.Bundle0004
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.Bundle0011
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.Bundle0010
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.OLiftSys
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0053
import Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientModuliObjectExists
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0055
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0640
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0636
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsEtIdealOfPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3686
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3579
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1604

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.OClsAt
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo

namespace UpperTheory.Gal.FiniteEtaleModels.O

private lemma nat_mem_of_isGen {A : Type} [CommRing A] {a : A} {N : ℕ} {𝔞 : Ideal A} (h : IsGen a N 𝔞) : (N : A) ∈ 𝔞 := by
  have h' : (Ideal.span {a} ⊔ Ideal.span {(N : A)}) * 𝔞 = Ideal.span {(N : A)} := h
  have hN : (N : A) ∈ Ideal.span {(N : A)} := Ideal.mem_span_singleton_self _
  rw [← h'] at hN
  exact (Ideal.mul_le_right : (Ideal.span {a} ⊔ Ideal.span {(N : A)}) * 𝔞 ≤ 𝔞) hN

theorem clsAt : ClsAt := by
  intro q _ D hm1 r hr R R' _ _ _ b gb β hmatch N N₀ c a 𝔞 hN hpos hcop hgen hue Y Ω _ _ y σ hyσ
  obtain ⟨o1, ⟨n1⟩⟩ := raise q D R R' b gb β hmatch N N₀ c hN hpos hcop Y.X Y.s Y.univ Ω y σ hyσ
  let o₀ := GlobalTheory.HTPullEvery.objPull Y.univ y (y ≫ Y.s) rfl
  let m := GlobalTheory.HTPullEvery.objPullMap Y.univ y (y ≫ Y.s) rfl
  have htr : ∀ {f f' : Sp Ω ⟶ Y.X} (_ : f = f') (n : QMap o1 Y.univ f c),
      ∃ n'' : QMap o1 Y.univ f' c, n''.φ = n.φ := by
    intro f f' h n
    subst h
    exact ⟨n, rfl⟩
  obtain ⟨n1', hn1'⟩ := htr (Category.id_comp y).symm n1
  obtain ⟨n, hn⟩ := (UpperTheory.quotient_map_comp q D R R' b gb N N₀ c (Sp Ω) (Sp Ω) Y.X σ (y ≫ Y.s) Y.s o1 o₀ Y.univ
    (𝟙 _) y).2.1 n1' m
  rw [hn1'] at hn
  obtain ⟨l, hl, hln⟩ := UpperTheory.quotient_level_of_lattice_generation UpperTheory.lattice_generation q D R R' b gb N N₀ c a 𝔞 hpos hgen (Sp Ω) σ (y ≫ Y.s) o1 o₀ n
  obtain ⟨lv', hlv', hlvm⟩ := isEtLev_exists_pull m Y.isLev
  obtain ⟨g₀, hg₀⟩ := Cmp.exists_levGrp hlv' hl
  obtain ⟨g, glin, gonto, ginj, giso, gtow, gN₀, gq⟩ := liftSys q D hm1 r hr 𝔞 N₀ hue hcop g₀
  obtain ⟨o', n', ho'⟩ := oResim q D R R' b gb N N₀ c hN hpos (Sp Ω) Y.X σ Y.s o1 Y.univ y n1 g
    ⟨glin, gonto, ginj, giso, gtow⟩ gN₀
  refine ⟨o', ⟨y, hyσ, n', fun y' => ?_⟩, rfl⟩
  have heta : o1.eta (g N (algebraMap (𝓞 D.F) D.O a • y')) = o1.eta (algebraMap (𝓞 D.F) D.O a • liftAct g₀ y') := by
    obtain ⟨z1, hz1⟩ := glin N hpos (algebraMap (𝓞 D.F) D.O a) y'
    have hq := gq N hpos (nat_mem_of_isGen hgen) y'
    have hdiff : g N y' - liftAct g₀ y' ∈ wSub D 𝔞 1 := by
      rw [← Submodule.Quotient.eq]
      rw [mk_liftAct]
      exact hq
    obtain ⟨z2, hz2⟩ := ((UpperTheory.lattice_generation q D a N 𝔞 hpos hgen).1 _).mpr hdiff
    have hsplit : algebraMap (𝓞 D.F) D.O a • g N y' =
        algebraMap (𝓞 D.F) D.O a • liftAct g₀ y' + N • z2 := by
      rw [← hz2, ← smul_add]
      congr 1
      abel
    rw [hz1, hsplit]
    have e1 := o1.eta_add (algebraMap (𝓞 D.F) D.O a • liftAct g₀ y' + N • z2) (N • z1)
    have e2 := o1.eta_add (algebraMap (𝓞 D.F) D.O a • liftAct g₀ y') (N • z2)
    have k1 : o1.eta (N • z1) = 1 := o1.eta_ker z1
    have k2 : o1.eta (N • z2) = 1 := o1.eta_ker z2
    rw [k1, _root_.mul_one] at e1
    rw [k2, _root_.mul_one] at e2
    exact e1.trans e2
  rw [ho', heta, ← hlvm, hg₀, ← hln, Category.assoc, ← hn]

end UpperTheory.Gal.FiniteEtaleModels.O
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PPtAll
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev GlobalTheory.UPel.HT.ES
open UpperTheory.Gal.FiniteEtaleModels

private theorem lev_pow {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) (𝔞 : Ideal (𝓞 D.F)) (r : ℕ) {T : Over S}
    (l : D.La → (T ⟶ o.A)) : IsEtLevOver o (𝔞 ^ r) 1 l ↔ IsEtLevOver o 𝔞 r l := by
  unfold IsEtLevOver wSub
  simp only [pow_one]

private theorem lev_top {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) {T : Over S} :
    IsEtLevOver o (⊤ : Ideal (𝓞 D.F)) 1 (fun _ : D.La => (1 : T ⟶ o.A)) := by
  have hw : ∀ y : D.La, y ∈ wSub D (⊤ : Ideal (𝓞 D.F)) 1 := by
    intro y
    refine Submodule.subset_span ⟨1, by simp, y, ?_⟩
    simp
  refine ⟨fun _ _ => (_root_.mul_one _).symm, fun c _ => ?_, fun _ _ => rfl, fun k _ _ x => ⟨fun y _ => hw y, fun g hg => ⟨0, ?_⟩⟩⟩
  · haveI := o.act.hom c
    exact (MonObj.one_comp _).symm
  · have h1 := hg 1 (by simp)
    rw [map_one, o.act.one, Category.comp_id] at h1
    rw [h1]
    exact MonObj.comp_one _

theorem UpperTheory.Gal.FiniteEtaleModels.ptAll_holds :
    IdealInd → CrtMul → PtAll := by
  intro hI hC p _ D R _ b N 𝔞 r hc he S s o k _ _ x
  have key : ∃ l : D.La → (Over.mk x ⟶ o.A), IsEtLevOver o (𝔞 ^ r) 1 l := by
    refine hI (𝓞 D.F) (IsEtPlace b)
      (fun 𝔠 => ∃ l : D.La → (Over.mk x ⟶ o.A), IsEtLevOver o 𝔠 1 l) ?_ ?_ ?_ (𝔞 ^ r)
      (pow_ne_zero _ he.1) ?_
    · exact ⟨_, lev_top o⟩
    · intro w e _ hw
      obtain ⟨l, hl⟩ := GlobalTheory.T.exists_etaleLevelStructure_at_geometricPoint p D R b N w e hc hw S s o k x
      exact ⟨l, (lev_pow o w e l).2 hl⟩
    · rintro 𝔟 𝔠 hbc ⟨l₁, h₁⟩ ⟨l₂, h₂⟩
      exact ⟨_, hC p D R b N S s o 𝔟 𝔠 hbc _ l₁ l₂ h₁ h₂⟩
    · intro w hw hle
      exact he.2 w hw (hw.isPrime.le_of_pow_le hle)
  obtain ⟨l, hl⟩ := key
  exact ⟨l, (lev_pow o 𝔞 r l).1 hl⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.StepAOf
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open GlobalTheory.UPel.HT.HeckeAd (IsTranslA heckeSubA)
open scoped TensorProduct

namespace UpperTheory.Gal.FiniteEtaleModels

theorem stepA_of (hD : DictP) (hX : SysExt) (hE : TrEtaK) (hK : TrKer) (hG : GalOfKer) (hH : BetaH) (hB : BetaLat) (hN : NumSplit)
    (hC : CoreA) (hE' : TrEta) (hBk : TrBack) (hQ : QComp) : StepA := by
  intro p _ D G L _ E _ _ gb w q _ r 𝔴 𝔫 S k T N₀ κ 𝔟₁ 𝔟₂ X₁ X₂ hle h hI hκ M₁ M₂ c₁ c₂ a₁ a₂ hn₁ hn₂ C₁ C₂ W
  obtain ⟨e₁, g₁⟩ : M₁.1 = N₀ * κ * c₁ ∧ IsGen a₁ M₁.1 𝔟₁ := hn₁
  obtain ⟨e₂, g₂⟩ : M₂.1 = N₀ * c₂ ∧ IsGen a₂ M₂.1 𝔟₂ := hn₂
  obtain ⟨l3, lq, lp, -, e, he⟩ := X₁.lev
  obtain ⟨l3', lq', -, -, -⟩ := X₂.lev
  have h₁ : 0 < M₁.1 := lt_of_lt_of_le (by norm_num) M₁.2.1
  have h₂ : 0 < M₂.1 := lt_of_lt_of_le (by norm_num) M₂.2.1
  have hNκ : 0 < N₀ * κ := by omega
  have hκ0 : 0 < κ := Nat.pos_of_mul_pos_left hNκ
  have hκp : κ.Coprime p := Nat.Coprime.coprime_dvd_left (dvd_mul_left _ _) lp
  have hκq : κ.Coprime q := Nat.Coprime.coprime_dvd_left (dvd_mul_left _ _) lq
  have hqe : ((q ^ e : ℕ) : 𝓞 D.F) ∈ 𝔟₁ := by
    rw [Nat.cast_pow]
    exact he (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_insert _ _)) e)
  obtain ⟨hmon, hlin, -, ⟨c', hc'p, hpol, hmult⟩, -⟩ := id W.trans
  obtain ⟨f, u, c, hcc, hsys, hrel⟩ := hD p D G L h κ c' hκ0 hκp hc'p hI hκ hmult
  obtain ⟨f', u', hsys', hff⟩ := hX D.toG p Fact.out f u c c' κ hcc hc'p hsys
  let F : D.La →+ D.La := f' (N₀ * κ)
  have hF : ∀ x, ∃ v ∈ LaHat D, κ • L.actG h⁻¹ (inAf D x) = inAf D (F x) + (N₀ * κ) • v := fun x => by
    obtain ⟨v, hv, ev⟩ := hrel _ hNκ lp x
    obtain ⟨z, hz⟩ : ∃ z : D.La, F x = f (N₀ * κ) x + (N₀ * κ) • z := hff _ hNκ lp x
    refine ⟨v - inAf D z, sub_mem hv (GlobalTheory.HeckeApprox.inAf_mem D z), ?_⟩
    rw [ev, hz, GlobalTheory.HeckeApprox.inAf_add, GlobalTheory.HeckeApprox.inAf_nsmul, smul_sub]
    abel
  have heta : ∀ y : D.La, (T.M M₁).univ.eta (c₁ • F y) ≫ W.ψ = W.o.eta (c₂ • y) := fun y => by
    refine hE p D G L E gb h _ _ M₁ M₂ _ _ W.ψ W.trans N₀ κ c₁ c₂ e₁ e₂ (F y) y ?_
    obtain ⟨v, hv, ev⟩ := hF y
    refine ⟨-L.actG h v, neg_mem (hI v hv), ?_⟩
    have := congrArg (L.actG h) ev
    rw [map_nsmul, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply, map_add, map_nsmul] at this
    rw [this, smul_neg]
    abel
  obtain ⟨n, m₁, m₂, a, hnQ, en₁, en₂, ea, ga⟩ := hN (𝓞 D.F) 𝔟₁ 𝔟₂ M₁.1 M₂.1 (q ^ e) a₁ a₂ h₁ h₂ hle g₁ g₂ hqe
  have hn0 : 0 < n := Nat.pos_of_mul_pos_right (en₁ ▸ h₁)
  have hm0 : 0 < m₁ := Nat.pos_of_mul_pos_left (en₁ ▸ h₁)
  obtain ⟨g, gl, gi, gs, gr⟩ := hH p D G L h κ n hn0 (Nat.Coprime.coprime_dvd_left ⟨m₁, en₁⟩ M₁.2.2)
    (Nat.Coprime.coprime_dvd_left hnQ (hκq.symm.pow_left e)) hI hκ
  obtain ⟨ρ, hρ, hρe⟩ := hB q (datAt S.atq S.sp) 𝔟₁ 𝔟₂ n m₁ a₁ a hn0 hm0 hle (en₁ ▸ g₁) ga g gl gi gs
  have hlv : ∀ y : D.La, (T.M M₁).univ.eta (algebraMap (𝓞 D.F) D.O a₁ • (ρ y : D.La)) ≫ W.ψ =
      W.o.eta (algebraMap (𝓞 D.F) D.O a₂ • y) := fun y => by
    obtain ⟨z, hz⟩ : ∃ z : D.La, m₁ • g (algebraMap (𝓞 D.F) D.O a • y) = algebraMap (𝓞 D.F) D.O a₁ • (ρ y : D.La) + (n * m₁) • z := hρe y
    have t₁ := hE' p D G L E gb h _ _ M₁ M₂ _ _ W.ψ W.trans n m₁ m₂ en₁ en₂ _ _ (gr (algebraMap (𝓞 D.F) D.O a • y))
    have t₂ : (T.M M₁).univ.eta (algebraMap (𝓞 D.F) D.O a₁ • (ρ y : D.La) + M₁.1 • z) =
        (T.M M₁).univ.eta (algebraMap (𝓞 D.F) D.O a₁ • (ρ y : D.La)) :=
      ((T.M M₁).univ.eta_add _ _).trans (by
        rw [show (T.M M₁).univ.eta (M₁.1 • z : D.La) = 1 from (T.M M₁).univ.eta_ker z, _root_.mul_one])
    have t₃ : algebraMap (𝓞 D.F) D.O a₂ • y = m₂ • algebraMap (𝓞 D.F) D.O a • y := by
      rw [ea, map_mul, map_natCast, mul_smul, Nat.cast_smul_eq_nsmul]
    rw [hz, ← en₁] at t₁
    rw [t₃, ← t₂]
    exact t₁
  obtain ⟨ψ', hm', b₁, b₂⟩ := hBk p D G L E gb h _ _ M₁ M₂ _ _ W.ψ W.trans κ hκp hκ
  have hdiv : κ ^ 2 / c = c' := by
    have hc0 : 0 < c := Nat.pos_of_mul_pos_right (hcc ▸ pow_pos hκ0 2)
    rw [← hcc, Nat.mul_div_cancel_left _ hc0]
  let o₁ := ob (D := datAt S.atq S.sp) (gb := gb) S.mat (T.M M₁).univ (N₀ * κ) c₁ e₁ h₁
  have hA : IsTranslA (D := datAt S.atq S.sp) F c κ N₀ o₁ (ob (D := datAt S.atq S.sp) (gb := gb) S.mat W.o N₀ c₂ e₂ h₂) W.ψ := by
    obtain ⟨hfin, hfree⟩ := HeckeAd.heckeSubA_finite_free S.b F κ N₀ hκ0 (by omega) hκq lq' _ o₁
    refine ⟨hmon, hlin, fun y => (heta y).symm, ?_, hdiv ▸ hpol, ⟨c', hcc.symm⟩⟩
    haveI := hmon
    refine hG _ _ _ (T.M M₁).univ.ab W.o.ab W.ψ ψ' κ hmon hm' b₁ b₂ (Hecke.Comp.isUnit_natCast S.b ((T.M M₁).s ≫ spMap (algebraMap (Ow w) E)) κ hκq) _ hfin ?_ hfree ?_
    · rintro _ ⟨x, rfl⟩
      show (T.M M₁).univ.eta (c₁ • N₀ • F x) ≫ W.ψ = 1
      rw [← map_nsmul, heta, smul_smul, mul_comm c₂, ← e₂]
      exact W.o.eta_ker x
    · intro Ω _ _ z y₀ hy₀
      obtain ⟨x, hx⟩ := hK p D G L E gb h _ _ M₁ M₂ _ _ W.ψ W.trans N₀ κ c₁ e₁ hκ F hF Ω z y₀ hy₀ (by
        haveI := hm'
        rw [← Category.comp_id y₀, ← MonObj.comp_pow, ← b₁, ← Category.assoc, hy₀, MonObj.one_comp])
      exact ⟨_, HeckeAd.mem_heckeSubA o₁ F N₀ x, hx⟩
  obtain ⟨n', hn'⟩ := (hQ q (datAt S.atq S.sp) (Ow w) E S.b gb M₂.1 N₀ c₂ _ _ _ _ _ _ (T.M M₂).univ X₂.Y.univ X₂.Y.univ C₂.j (𝟙 _)).2.2.2
    _ _ W.o W.π W.φ C₂.m
  let C₂' : Cls (D := datAt S.atq S.sp) (gb := gb) X₂.Y (algebraMap (Ow w) E) W.o c₂ a₂ :=
    { j := W.π ≫ C₂.j
      ov := by rw [Category.assoc, C₂.ov, ← Category.assoc, W.ov]
      m := n'
      lv := fun y => by
        rw [hn', ← Category.assoc]
        erw [W.φ.eta]
        rw [Category.assoc, Category.assoc]
        exact congrArg _ (C₂.lv y) }
  haveI : Smooth X₁.M.s := X₁.M.smooth.smooth
  haveI := X₁.et
  haveI : IsLocallyNoetherian X₁.Y.X := LocallyOfFiniteType.isLocallyNoetherian (X₁.π ≫ X₁.M.s)
  obtain ⟨t, Φ, ht, hΦ, j₁, j₂⟩ := hC q (datAt S.atq S.sp) (Ow w) E S.b gb _ S.mat N₀ κ c 𝔟₁ 𝔟₂ X₁.Y X₂.Y this l3' lq' hκq ⟨c', hcc.symm⟩ hle
    ⟨e, hqe⟩ f' u' (hsys'.mono q) ρ hρ _ _ M₁.1 M₂.1 c₁ c₂ a₁ a₂ e₁ e₂ h₁ h₂ g₂ (T.M M₁).univ W.o W.ψ hA hlv C₁ C₂'
  exact ⟨⟨t, ht, Φ, hΦ⟩, j₁, j₂.trans (by rw [← hn'])⟩

end UpperTheory.Gal.FiniteEtaleModels
end
end


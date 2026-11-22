import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpecHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericHeckeMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2339
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0049

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransPull
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem pow_push {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (d : ℕ) :
    ((𝟙 G') ^ d : G' ⟶ G').left ≫ φ = φ ≫ ((𝟙 G) ^ d : G ⟶ G).left := by
  obtain ⟨hpb, hm⟩ := h
  have hw : φ ≫ G.hom = G'.hom ≫ f := hpb.w
  let P : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk φ (by simpa using hw)
  have key : ∀ n : ℕ, ((𝟙 G') ^ n : G' ⟶ G').left ≫ φ = (P ^ n).left := by
    intro n
    induction n with
    | zero =>
      let x₀ : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk ((1 : G' ⟶ G').left ≫ φ)
        (by rw [Category.assoc, hw, ← Category.assoc, Over.w]; rfl)
      have e : (x₀ * x₀).left = x₀.left := by
        rw [hm G' 1 1 x₀ x₀ rfl rfl, _root_.mul_one (1 : G' ⟶ G')]
        rfl
      have e2 : x₀ * x₀ = x₀ := Over.OverMorphism.ext e
      have e3 : x₀ = 1 := by simpa using e2
      rw [pow_zero, pow_zero]
      exact congrArg CommaMorphism.left e3
    | succ n ih =>
      rw [pow_succ, pow_succ, ← hm G' _ _ (P ^ n) P ih.symm (by simp [P])]
  rw [key d]
  have hP : P ≫ ((𝟙 G) ^ d) = P ^ d := by rw [MonObj.comp_pow, Category.comp_id]
  rw [← hP]
  rfl

private theorem qinv_pull {S S' : Scheme.{0}} {A₁' A₂' : Over S'} {A₁ A₂ : Over S} [GrpObj A₁'] [GrpObj A₁] {f : S' ⟶ S}
    {φ₁ : A₁'.left ⟶ A₁.left} {φ₂ : A₂'.left ⟶ A₂.left} (c₁ : IsGrpPullback A₁' A₁ f φ₁) {ψ : A₁ ⟶ A₂} {χ : A₂ ⟶ A₁}
    {ψ' : A₁' ⟶ A₂'} {χ' : A₂' ⟶ A₁'} (e : ψ'.left ≫ φ₂ = φ₁ ≫ ψ.left) (e' : χ'.left ≫ φ₁ = φ₂ ≫ χ.left) {d : ℕ}
    (h : ψ ≫ χ = (𝟙 A₁) ^ d) : ψ' ≫ χ' = (𝟙 A₁') ^ d := by
  apply Over.OverMorphism.ext
  apply c₁.1.hom_ext
  · rw [Over.comp_left, Category.assoc, e', ← Category.assoc, e, Category.assoc, ← Over.comp_left, h, pow_push c₁]
  · rw [Over.w, Over.w]

theorem UpperTheory.Gal.G3.pTransPull :
    HomPull → TatePull → TransPull := by
  intro hHom hTate p _ D G L R _ _ gb S S' s s' f hf N₁ N₂ o₁ o₂ o₁' o₂' m₁ m₂ ψ h hT
  obtain ⟨hmon, hact, ⟨χ, d, hχmon, hχact, e1, e2, hd⟩, ⟨c, hc, ⟨lb⟩, tt⟩, hgeo⟩ := hT
  obtain ⟨ψ', hψ, hmon', hact', hlb'⟩ := hHom D.toG R gb S S' s s' f N₁ N₂ o₁ o₂ o₁' o₂' m₁ m₂ ψ
  obtain ⟨χ', hχ, hχmon', hχact', -⟩ := hHom D.toG R gb S S' s s' f N₂ N₁ o₂ o₁ o₂' o₁' m₂ m₁ χ
  refine ⟨ψ', ⟨hmon' hmon, hact' hact, ⟨χ', d, hχmon' hχmon, hχact' hχact, qinv_pull m₁.cart hψ hχ e1,
    qinv_pull m₂.cart hχ hψ e2, hd⟩, ⟨c, hc, hlb' c ⟨lb⟩, tt⟩, ?_⟩, hψ⟩
  intro k _ _ t β ht
  obtain ⟨I₁, I₂, hI₁, hI₂, hev⟩ := hgeo k (t ≫ f) β (by rw [Category.assoc, hf, ht])
  obtain ⟨I₁', hI₁', hev₁⟩ := (hTate p D R gb S S' s s' f N₁ o₁ o₁' m₁ k t).1 I₁
  obtain ⟨I₂', hI₂', hev₂⟩ := (hTate p D R gb S S' s s' f N₂ o₂ o₂' m₂ k t).1 I₂
  refine ⟨I₁', I₂', hI₁' hI₁, hI₂' hI₂, fun n hn hnp x y => ?_⟩
  rw [← hev n hn hnp x y]
  constructor
  · intro e
    apply Over.OverMorphism.ext
    have key := congrArg (fun a => a.left ≫ m₂.φ) e
    simp only [Over.comp_left, Category.assoc, hψ] at key
    erw [← Category.assoc, hev₁ n x, hev₂ n y] at key
    rw [Over.comp_left]
    exact key
  · intro e
    apply Over.OverMorphism.ext
    apply m₂.cart.1.hom_ext
    · rw [Over.comp_left, Category.assoc, hψ, ← Category.assoc]
      erw [hev₁ n x, hev₂ n y]
      rw [← Over.comp_left, e]
    · rw [Over.w, Over.w]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransSelf
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem pol_one {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] [Algebra ℚ R]
    {gb : GBase D.toG R} {S : Scheme.{0}} {s : S ⟶ Sp R} {N : ℕ} (o : GObj gb N s) :
    Nonempty (LBIso (Hecke.lbPow o.P 1) (o.P.pull (Hecke.sq2 (𝟙 o.A)))) := by
  have h : Hecke.sq2 (𝟙 o.A) = 𝟙 _ := by simp [Hecke.sq2]
  refine ⟨?_⟩
  rw [h]
  unfold Hecke.lbPow LB.pull
  exact (GlobalTheory.PrimNorm.lbIso_iff o.isLB _ _ _ _).2 rfl

private theorem gTateIso_ev_nsmul' {G : GDatum} {k : Type} [Field k] {Q : Type} [Group Q]
    {act : G.O → Q → Q} {e : ℕ → Q → Q → kˣ → Prop} (I : GTateIso G k Q act e) (n c : ℕ)
    (y : G.La) : I.ev n (c • y) = I.ev n y ^ c := by
  induction c with
  | zero =>
    have h := I.add n 0 0
    rw [add_zero] at h
    have h1 : I.ev n 0 = 1 :=
      mul_left_cancel (a := I.ev n 0) (by rw [_root_.mul_one]; exact h.symm)
    rw [zero_smul, pow_zero, h1]
  | succ c ih => rw [succ_nsmul, I.add, ih, pow_succ]

theorem UpperTheory.Gal.G3.pTransSelf :
    MultBasic → RelComp → TateTwist → TransSelf := by
  intro hM hR hT p _ D G L R _ _ gb S s N
  refine ⟨fun o u hu => ?_, fun c hN hc o => ?_⟩
  · have hu1 : u ∈ L.KN 1 := UpperTheory.Gal.Int.Geo.KN_anti (one_dvd _) hu
    obtain ⟨a, a', ha, ha', haa, heq⟩ := (hM p).2.2 D G L u hu1
    refine ⟨⟨by simp, by simp⟩, fun _ => by simp, ⟨𝟙 _, 1, ⟨by simp, by simp⟩, fun _ => by simp,
      by simp, by simp, Nat.coprime_one_left _⟩, ⟨1, Nat.coprime_one_left _, pol_one o, a, a', ha,
      ha', haa, heq⟩, ?_⟩
    intro k _ _ x β hβ
    obtain ⟨I, hI⟩ := o.geom k x β hβ
    obtain ⟨J, hJ, hRel⟩ := hT p D G L R gb S s N o k x I hI u hu
    exact ⟨I, J, hI, hJ, hRel⟩
  · obtain ⟨a, a', ha, ha', haa, heq⟩ := (hM p).2.2 D G L 1 (one_mem _)
    have hmon : IsMonHom (𝟙 o.A) := ⟨by simp, by simp⟩
    refine ⟨show IsMonHom (𝟙 o.A) from hmon, fun _ => by simp [GObj.forgetMul],
      ⟨𝟙 _, 1, show IsMonHom (𝟙 o.A) from hmon,
      fun _ => by simp [GObj.forgetMul], by simp; exact Category.comp_id _,
      by simp; exact Category.comp_id _, Nat.coprime_one_left _⟩,
      ⟨1, Nat.coprime_one_left _, pol_one o, a, a', ha, ha', haa, heq⟩, ?_⟩
    intro k _ _ x β hβ
    obtain ⟨I, hI⟩ := o.geom k x β hβ
    have hInt : UpperTheory.Gal.Int.Geo.Integ L 1 := UpperTheory.Gal.Int.Geo.integ_of_mem (one_mem _)
    refine ⟨I, I, hI, fun y => ?_, ?_⟩
    · show toUnit _ ≫ o.eta (c • y) = _
      rw [hI, gTateIso_ev_nsmul', I.tower _ _ hN hc]
    · exact (hR p D G L R gb S s _ _ _ o o o k x I I I (𝟙 _) (𝟙 _) 1 1 hmon hmon hInt).1
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransUniqPt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pTransUniqPt :
    MultBasic → IsogFEt → TransKer → QuotUniq → PolUniq → MapOfIso → TransUniqPt := by
  intro hMB hFE hTK hQU hPU hMI p _ D G L R _ _ gb k _ _ s N' N o o₁ o₂ ψ₁ ψ₂ h hint hadm tr₁ tr₂
  have hK := hTK p D G L R gb (Sp k) s N' N o o₁ o₂ ψ₁ ψ₂ h hint hadm tr₁ tr₂
  obtain ⟨mon₁, -, ⟨ψ₁', d₁, mon₁', -, e₁, e₁', cop₁⟩, ⟨c₁, hc₁, ⟨lb₁⟩, t₁, t₁', i₁, i₁', tt₁, hm₁⟩, -⟩ := id tr₁
  obtain ⟨mon₂, -, ⟨ψ₂', d₂, mon₂', -, e₂, e₂', cop₂⟩, ⟨c₂, hc₂, ⟨lb₂⟩, t₂, t₂', i₂, i₂', tt₂, hm₂⟩, -⟩ := id tr₂
  have dpos : ∀ d : ℕ, d.Coprime p → 0 < d := fun d hd => Nat.pos_of_ne_zero fun h0 => by
    subst h0
    exact (Fact.out : p.Prime).one_lt.ne' (by simpa using hd)
  obtain ⟨f₁, et₁, sj₁⟩ := hFE R (Sp k) s o.A o₁.A o.ab o₁.ab ψ₁ ψ₁' d₁ (dpos _ cop₁) mon₁ mon₁' e₁ e₁'
  obtain ⟨f₂, et₂, sj₂⟩ := hFE R (Sp k) s o.A o₂.A o.ab o₂.ab ψ₂ ψ₂' d₂ (dpos _ cop₂) mon₂ mon₂' e₂ e₂'
  obtain ⟨θ, isoθ, monθ, hθ⟩ := hQU k o.A o₁.A o₂.A o.ab o₁.ab o₂.ab ψ₁ ψ₂ mon₁ mon₂ f₁ et₁ sj₁ f₂ et₂ sj₂
    (fun Ω _ _ t a => (hK Ω t).1 a)
  have lin₁ := tr₁.2.1
  have lin₂ := tr₂.2.1
  haveI := f₁
  haveI := et₁
  haveI := sj₁
  haveI : Epi ψ₁.left := Flat.epi_of_flat_of_surjective _
  have cancel : ∀ {X : Over (Sp k)} (a b : o₁.A ⟶ X), ψ₁ ≫ a = ψ₁ ≫ b → a = b := fun a b e =>
    Over.OverMorphism.ext ((cancel_epi ψ₁.left).1 (by simpa using congrArg (·.left) e))
  have lin : ∀ c, o₁.act.act c ≫ θ = θ ≫ o₂.act.act c := fun c => cancel _ _ (by
    rw [← Category.assoc, ← lin₁ c, Category.assoc, hθ, lin₂ c, ← hθ, Category.assoc])
  have hcc : c₁ = c₂ := (hMB p).1 (mul h) c₁ c₂ hc₁ hc₂ ⟨t₁, t₁', i₁, i₁', tt₁, hm₁⟩ ⟨t₂, t₂', i₂, i₂', tt₂, hm₂⟩
  subst hcc
  have hPo := o.isLB
  have hP1 := o₁.isLB
  have hP2 := o₂.isLB
  have hQ : (o₂.P.pull (Hecke.sq2 θ)).IsLB := pull_isLB hP2 _
  have sqc : Hecke.sq2 ψ₁ ≫ Hecke.sq2 θ = Hecke.sq2 ψ₂ := by
    rw [← hθ]
    simp only [Hecke.sq2, ← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, Category.assoc]
  have key : LBIso (o₁.P.pull (Hecke.sq2 ψ₁)) ((o₂.P.pull (Hecke.sq2 θ)).pull (Hecke.sq2 ψ₁)) := by
    refine (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hP1 _) (pull_isLB hQ _)).1 ?_
    have a1 := (GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb hPo _ _) (pull_isLB hP1 _)).2 lb₁
    have a2 := (GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb hPo _ _) (pull_isLB hP2 _)).2 lb₂
    rw [← a1, a2, GlobalTheory.CechPic.cls_pull hP2, GlobalTheory.CechPic.cls_pull hQ, GlobalTheory.CechPic.cls_pull hP2,
      ← GlobalTheory.CechPic.pull_comp, sqc]
  have r₁ : ∃ t : ((o₂.P.pull (Hecke.sq2 θ)).pull (lift (1 : o₁.A ⟶ o₁.A) (𝟙 o₁.A)).left).Gen, t.IsGen := by
    refine (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hQ _)).1 ?_
    have e : (lift (1 : o₁.A ⟶ o₁.A) (𝟙 o₁.A)).left ≫ Hecke.sq2 θ =
        θ.left ≫ (lift (1 : o₂.A ⟶ o₂.A) (𝟙 o₂.A)).left := by
      simp only [Hecke.sq2, ← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, Category.id_comp,
        Category.comp_id, one_comp, comp_one]
    rw [GlobalTheory.CechPic.cls_pull hQ, GlobalTheory.CechPic.cls_pull hP2, ← GlobalTheory.CechPic.pull_comp, e, GlobalTheory.CechPic.pull_comp,
      ← GlobalTheory.CechPic.cls_pull hP2 _ (pull_isLB hP2 _), (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hP2 _)).2 o₂.rig₁, map_zero]
  have r₂ : ∃ t : ((o₂.P.pull (Hecke.sq2 θ)).pull (lift (𝟙 o₁.A) (1 : o₁.A ⟶ o₁.A)).left).Gen, t.IsGen := by
    refine (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hQ _)).1 ?_
    have e : (lift (𝟙 o₁.A) (1 : o₁.A ⟶ o₁.A)).left ≫ Hecke.sq2 θ =
        θ.left ≫ (lift (𝟙 o₂.A) (1 : o₂.A ⟶ o₂.A)).left := by
      simp only [Hecke.sq2, ← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, Category.id_comp,
        Category.comp_id, one_comp, comp_one]
    rw [GlobalTheory.CechPic.cls_pull hQ, GlobalTheory.CechPic.cls_pull hP2, ← GlobalTheory.CechPic.pull_comp, e, GlobalTheory.CechPic.pull_comp,
      ← GlobalTheory.CechPic.cls_pull hP2 _ (pull_isLB hP2 _), (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hP2 _)).2 o₂.rig₂, map_zero]
  have pol : LBIso o₁.P (o₂.P.pull (Hecke.sq2 θ)) :=
    hPU (Sp k) o.A o₁.A o.ab o₁.ab ψ₁ mon₁ f₁ et₁ sj₁ o₁.P _ hP1 hQ o₁.rig₁ o₁.rig₂ r₁ r₂ key
  have lev : ∀ y, o₁.eta y ≫ θ = o₂.eta y := by
    intro y
    obtain ⟨v, hv⟩ := sj₁.surj (UpperTheory.Gal.TranscendenceTraces.pt (toUnit (Over.mk (𝟙 (Sp k))) ≫ o₁.eta y).left)
    obtain ⟨z, hz, -⟩ := UpperTheory.Gal.TranscendenceTraces.ptLift_holds ψ₁.left k (toUnit (Over.mk (𝟙 (Sp k))) ≫ o₁.eta y).left v hv
    let a : Over.mk (𝟙 (Sp k)) ⟶ o.A := Over.homMk z (by
      have w1 := Over.w ψ₁
      have w2 := Over.w (toUnit (Over.mk (𝟙 (Sp k))) ≫ o₁.eta y)
      simp only [Over.mk_hom] at w2 ⊢
      rw [← w1, ← Category.assoc, hz, w2])
    have ha : a ≫ ψ₁ = toUnit _ ≫ o₁.eta y := Over.OverMorphism.ext hz
    have hb := ((hK k (𝟙 _)).2 a y).1 ha
    have e : toUnit (Over.mk (𝟙 (Sp k))) ≫ o₁.eta y ≫ θ = toUnit (Over.mk (𝟙 (Sp k))) ≫ o₂.eta y := by
      rw [← Category.assoc, ← ha, Category.assoc, hθ, hb]
    let i : 𝟙_ (Over (Sp k)) ⟶ Over.mk (𝟙 (Sp k)) := Over.mkIdTerminal.from _
    have hi : i ≫ toUnit (Over.mk (𝟙 (Sp k))) = 𝟙 _ := toUnit_unique _ _
    have e' := congrArg (i ≫ ·) e
    simpa [← Category.assoc, hi] using e'
  obtain ⟨m, hm⟩ := hMI D.toG R gb (Sp k) s N.1 o₁ o₂ θ isoθ monθ lin pol lev
  exact ⟨m, by rw [hm, ← hθ, Over.comp_left]⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTwFEt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem card_eq_relIndex {G Γ : Type} [Group G] (H L : Subgroup G) (r : Γ → G) (hr : ∀ x, r x ∈ L)
    (hu : ∀ k ∈ L, ∃! x, k * (r x)⁻¹ ∈ H) : Nat.card Γ = H.relIndex L := by
  unfold Subgroup.relIndex Subgroup.index
  refine Nat.card_congr (Equiv.ofBijective
    (fun x => (QuotientGroup.mk ⟨(r x)⁻¹, L.inv_mem (hr x)⟩ : L ⧸ H.subgroupOf L)) ⟨?_, ?_⟩)
  · intro x y e
    have e' := QuotientGroup.eq.mp e
    have h2 : r x * (r y)⁻¹ ∈ H := by simpa [Subgroup.mem_subgroupOf] using e'
    have h1 : r x * (r x)⁻¹ ∈ H := by simp [H.one_mem]
    exact (hu (r x) (hr x)).unique h1 h2
  · intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨x, hx, -⟩ := hu (g : G)⁻¹ (L.inv_mem g.2)
      refine ⟨x, QuotientGroup.eq.mpr ?_⟩
      rw [Subgroup.mem_subgroupOf]
      have h3 := H.inv_mem hx
      simpa using h3

private theorem fEt_normal (hb : FEtBasic) (hg : TwGal) {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G)
    (m j : X.ι) (b : X.admitted m j 1) (hn : ∀ k ∈ X.K j, ∀ u ∈ X.K m, k * u * k⁻¹ ∈ X.K m) :
    FEt (X.tr m j 1 b.1 b.2) ((X.K m).relIndex (X.K j)) := by
  obtain ⟨Γ, _, _, r, c, hr, hu, hG⟩ := hg X m j b hn
  rw [← card_eq_relIndex _ _ r hr hu]
  exact hb.2.2 _ Γ _ hG

theorem UpperTheory.Gal.G3.pTwFEt :
    FEtBasic → TwGal → TwFEt := by
  intro hb hg B G _ X i j a
  obtain ⟨m, hmj, hn, hS⟩ := X.deep j {(i, 1)}
  have hmi : X.K m ≤ X.K i := fun u hu => by simpa using hS (i, 1) (by simp) u hu
  have hij : X.K i ≤ X.K j := fun u hu => by simpa using a.2 u hu
  have b : X.admitted m j 1 := ⟨a.1, fun u hu => by simpa using hmj hu⟩
  have b' : X.admitted m i 1 := ⟨a.1, fun u hu => by simpa using hmi hu⟩
  have h1 := fEt_normal hb hg X m j b hn
  have h2 := fEt_normal hb hg X m i b' (fun k hk u hu => hn k (hij hk) u hu)
  have hc : X.tr m i 1 b'.1 b'.2 ≫ X.tr i j 1 a.1 a.2 = X.tr m j 1 b.1 b.2 := by
    have e : ∀ (h : G) (_ : h = 1) p q, X.tr m j h p q = X.tr m j 1 b.1 b.2 := by
      rintro _ rfl _ _; rfl
    rw [X.tr_mul m i j 1 1 b'.1 b'.2 a.1 a.2 (by simpa using a.1) (by simpa using b.2)]
    exact e _ (mul_one 1) _ _
  refine ⟨X.fin i j a.1 a.2, X.etale i j a.1 a.2, fun K _ _ x => ?_⟩
  set s := X.tr i j 1 a.1 a.2 with hs
  set r := X.tr m i 1 b'.1 b'.2 with hr
  have fs : Finite {y : Spec (CommRingCat.of K) ⟶ X.Z i // y ≫ s = x} :=
    have := X.fin i j a.1 a.2
    (UpperTheory.Gal.TranscendenceTraces.fibFin_holds s K x).to_subtype
  have fr : ∀ y : {y : Spec (CommRingCat.of K) ⟶ X.Z i // y ≫ s = x},
      Finite {w : Spec (CommRingCat.of K) ⟶ X.Z m // w ≫ r = y.1} := fun y =>
    have := X.fin m i b'.1 b'.2
    (UpperTheory.Gal.TranscendenceTraces.fibFin_holds r K y.1).to_subtype
  have := Fintype.ofFinite {y : Spec (CommRingCat.of K) ⟶ X.Z i // y ≫ s = x}
  have e1 : {w : Spec (CommRingCat.of K) ⟶ X.Z m // w ≫ X.tr m j 1 b.1 b.2 = x} ≃
      Σ y : {y : Spec (CommRingCat.of K) ⟶ X.Z i // y ≫ s = x},
        {w : Spec (CommRingCat.of K) ⟶ X.Z m // w ≫ r = y.1} :=
    { toFun := fun w => ⟨⟨w.1 ≫ r, by rw [Category.assoc, hc, w.2]⟩, ⟨w.1, rfl⟩⟩
      invFun := fun p => ⟨p.2.1, by rw [← hc, ← Category.assoc, p.2.2, p.1.2]⟩
      left_inv := fun w => rfl
      right_inv := by
        rintro ⟨⟨y, hy⟩, ⟨w, hw⟩⟩
        change w ≫ r = y at hw
        subst hw
        rfl }
  have hcount : Nat.card {y : Spec (CommRingCat.of K) ⟶ X.Z i // y ≫ s = x} * (X.K m).relIndex (X.K i) =
      (X.K m).relIndex (X.K j) := by
    rw [← h1.2.2 K x, Nat.card_congr e1, Nat.card_sigma]
    simp only [h2.2.2 K, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [Nat.card_eq_fintype_card]
  have hmul := Subgroup.relIndex_mul_relIndex (X.K m) (X.K i) (X.K j) hmi hij
  have hpos : 0 < (X.K m).relIndex (X.K i) := Nat.pos_of_ne_zero (X.idx m i)
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [hmul, ← hcount, mul_comm]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTwMem
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
open GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh
universe u

private theorem sp_sub (Ω : Type) [Field Ω] : Subsingleton (UpperTheory.Gal.G3.sp Ω) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum Ω))

private theorem pt_factor {Ω : Type} [Field Ω] {I : Type} [Finite I] {Y : Scheme.{0}}
    (y : UpperTheory.Gal.G3.sp Ω ⟶ ∐ (fun _ : I => Y)) : ∃ (c : I) (y₀ : UpperTheory.Gal.G3.sp Ω ⟶ Y), y₀ ≫ Sigma.ι (fun _ : I => Y) c = y := by
  haveI := sp_sub Ω
  let pt : UpperTheory.Gal.G3.sp Ω := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum Ω)
  obtain ⟨c, v, hv⟩ := (sigmaOpenCover (fun _ : I => Y)).exists_eq (y pt)
  have hι : (sigmaOpenCover (fun _ : I => Y)).f c = Sigma.ι (fun _ : I => Y) c := rfl
  rw [hι] at hv
  refine ⟨c, IsOpenImmersion.lift (Sigma.ι (fun _ : I => Y) c) y ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨w, rfl⟩
  exact ⟨v, hv.trans (by rw [Subsingleton.elim w pt])⟩

private theorem pt_index {Ω : Type} [Field Ω] {I : Type} [Finite I] {Y : Scheme.{0}} {c d : I}
    (y z : UpperTheory.Gal.G3.sp Ω ⟶ Y) (h : y ≫ Sigma.ι (fun _ : I => Y) c = z ≫ Sigma.ι (fun _ : I => Y) d) : c = d := by
  let pt : UpperTheory.Gal.G3.sp Ω := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum Ω)
  have e : Sigma.ι (fun _ : I => Y) c (y pt) = Sigma.ι (fun _ : I => Y) d (z pt) := by
    have := congrArg (fun f : UpperTheory.Gal.G3.sp Ω ⟶ ∐ (fun _ : I => Y) => f pt) h
    simpa using this
  exact congrArg Sigma.fst ((sigmaι_eq_iff (fun _ : I => Y) c d _ _).mp e)

theorem UpperTheory.Gal.G3.pTwMem :
    SplitsPts → PtsOfSplits → SigmaFEt → TwFEt → TwSplit → TwMem.{u} := by
  intro hS hP hSg hF hT B G _ X F _ T m i j a hmi hn I A _ _ e he r hr hu ht tr htr x
  have hij : X.K i ≤ X.K j := fun u hu' => by simpa using a.2 u hu'
  have b : X.admitted m j 1 := X.isAdmissibleIntegralBasisChange_one (hmi.trans hij)
  have ar : ∀ y, X.admitted m i (r y) := fun y =>
    ⟨X.K_le j _ (hr y), fun u hu' => hmi (hn _ (hr y) u hu')⟩
  obtain ⟨hfin, het, -⟩ := hSg (X.tr i j 1 a.1 a.2) _ I (hF X i j a)
  have hsp := hT X m i j a b hmi hn A r ar hr hu
  let σ : I × A → (X.Z m ⟶ ∐ fun _ : I => X.Z i) := fun z =>
    X.tr m i (r z.2) (ar z.2).1 (ar z.2).2 ≫ Sigma.ι (fun _ : I => X.Z i) z.1
  have hσs : ∀ z, σ z ≫ (Sigma.desc fun _ : I => X.tr i j 1 a.1 a.2) = X.tr m j 1 b.1 b.2 := by
    intro z
    simp only [σ, Category.assoc, Sigma.ι_desc]
    exact hsp.choose z.2
  have split : Splits (Sigma.desc fun _ : I => X.tr i j 1 a.1 a.2) (X.tr m j 1 b.1 b.2) σ := by
    refine hS _ _ (I × A) σ hσs ?_
    intro Ω _ _ w y hy
    obtain ⟨c, y₀, rfl⟩ := pt_factor y
    have hy₀ : y₀ ≫ X.tr i j 1 a.1 a.2 = w ≫ X.tr m j 1 b.1 b.2 := by
      rw [← hy, Category.assoc, Sigma.ι_desc]
    obtain ⟨d, hd, hd'⟩ := hP _ _ A _ hsp Ω w y₀ hy₀
    refine ⟨(c, d), ?_, ?_⟩
    · show w ≫ X.tr m i (r d) (ar d).1 (ar d).2 ≫ Sigma.ι (fun _ : I => X.Z i) c = _
      rw [← Category.assoc, hd]
    · rintro ⟨c', d'⟩ h
      have h' : (w ≫ X.tr m i (r d') (ar d').1 (ar d').2) ≫ Sigma.ι (fun _ : I => X.Z i) c' =
          y₀ ≫ Sigma.ι (fun _ : I => X.Z i) c := by
        rw [Category.assoc]; exact h
      obtain rfl : c' = c := pt_index _ _ h'
      have hm := (cancel_mono (Sigma.ι (fun _ : I => X.Z i) c')).mp h'
      rw [hd' d' hm]
  have hq : ∀ z, σ z ≫ (Sigma.desc fun _ : I => X.tr i j 1 a.1 a.2) ≫ X.q j = X.q m := by
    intro z
    rw [← Category.assoc, hσs, X.tr_q]
  have key := htr (X.Z m) (X.q m) (X.tr m j 1 b.1 b.2) (X.tr_q ..) (I × A) σ hq split
    (T.pull _ ht x)
  rw [X.pl_eq T b, key, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun y _ => ?_
  have ad : X.admitted m j (e c * r y) := (ar y).mul (he c)
  have e1 : σ (c, y) ≫ (Sigma.desc fun c : I => X.tr i j (e c) (he c).1 (he c).2) =
      X.tr m j (e c * r y) ad.1 ad.2 := by
    simp only [σ, Category.assoc, Sigma.ι_desc]
    exact X.tr_mul m i j _ _ _ _ _ _ _ _
  rw [X.pl_eq T ad, ← T.pull_comp _ _ (hq (c, y)) ht (by rw [e1, X.tr_q])]
  simp only [e1]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PWitComp
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

namespace UpperTheory.Gal.G3

section Maps

open GlobalTheory.UPel.HT.Hecke

variable {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R]

private theorem exists_map_id {b : GBase G R} {N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R} (o : GObj b N s) :
    ∃ m : GObjMap o o (𝟙 S), m.φ = 𝟙 _ :=
  ⟨{ φ := 𝟙 _, φ₂ := 𝟙 _, cart := GlobalTheory.SiegLower.isGrpPullback_id o.A, sq := ⟨by simp, by simp⟩,
     act := fun c => by simp, pol := GlobalTheory.SiegLower.lbIso_pull_id o.isLB, eta := fun y => by simp }, rfl⟩

private theorem exists_map_comp {b : GBase G R} {N : ℕ} {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R}
    {s₃ : S₃ ⟶ Sp R} {o₁ : GObj b N s₁} {o₂ : GObj b N s₂} {o₃ : GObj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃}
    (h₁ : GObjMap o₁ o₂ f) (h₂ : GObjMap o₂ o₃ g) : ∃ m : GObjMap o₁ o₃ (f ≫ g), m.φ = h₁.φ ≫ h₂.φ := by
  have sq : IsSquare (h₁.φ ≫ h₂.φ) (h₁.φ₂ ≫ h₂.φ₂) := by
    constructor
    · rw [Category.assoc, h₂.sq.1, ← Category.assoc, h₁.sq.1, Category.assoc]
    · rw [Category.assoc, h₂.sq.2, ← Category.assoc, h₁.sq.2, Category.assoc]
  have act : ∀ c, (o₁.act.act c).left ≫ (h₁.φ ≫ h₂.φ) = (h₁.φ ≫ h₂.φ) ≫ (o₃.act.act c).left := by
    intro c
    rw [← Category.assoc, h₁.act, Category.assoc, h₂.act, Category.assoc]
  have eta : ∀ y, (o₁.eta y).left ≫ (h₁.φ ≫ h₂.φ) = (f ≫ g) ≫ (o₃.eta y).left := by
    intro y
    rw [← Category.assoc, h₁.eta, Category.assoc, h₂.eta, Category.assoc]
  have H : LBIso (o₂.P.pull h₁.φ₂) ((o₃.P.pull h₂.φ₂).pull h₁.φ₂) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o₂.P h₁.φ₂ h₁.φ₂ rfl)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (o₃.P.pull h₂.φ₂) h₁.φ₂ h₁.φ₂ rfl) h₂.pol
  have H' : LBIso (o₂.P.pull h₁.φ₂) (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.chartPull (chartPullId _) (chartPullIn o₃.P (fun _ : PUnit => h₂.φ₂) (fun _ => 1) h₁.φ₂) H
  have pol : LBIso o₁.P (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) h₁.pol H'
  exact ⟨⟨h₁.φ ≫ h₂.φ, h₁.φ₂ ≫ h₂.φ₂, h₁.cart.comp h₂.cart, sq, act, pol, eta⟩, rfl⟩

end Maps

end UpperTheory.Gal.G3

theorem UpperTheory.Gal.G3.pWitComp :
    TransSelf → TransComp → TransPull → WitComp := by
  intro hS hC hP
  intro p _ D G L R _ _ gb N₁ N₂ N₃ X₁ X₂ X₃ h h'
  refine ⟨fun u hu => ?_, fun hI hA π Φ π' Φ' hW hW' => ?_⟩
  · obtain ⟨m, hm⟩ := exists_map_id X₁.univ
    refine ⟨by simp, X₁.univ, 𝟙 _, m, (hS p D G L R gb X₁.X X₁.s N₁).1 X₁.univ u hu, ?_⟩
    rw [hm]
    simp
  · obtain ⟨hπ, o, ψ, φ, hT, hΦ⟩ := hW
    obtain ⟨hπ', o', ψ', φ', hT', hΦ'⟩ := hW'
    obtain ⟨o'', ⟨m''⟩⟩ := UpperTheory.exists_levelObj_pullback_of_charZero X₁.s π hπ o'
    obtain ⟨ψ'', hT'', hsq⟩ := hP p D G L R gb X₂.X X₁.X X₂.s X₁.s π hπ _ _ X₂.univ o' o o'' φ m'' ψ' h' hT'
    have hTT := hC p D G L R gb X₁.X X₁.s N₁ N₂ N₃ X₁.univ o o'' ψ ψ'' h h' hI hA hT hT''
    obtain ⟨mm, hmm⟩ := exists_map_comp m'' φ'
    refine ⟨by rw [Category.assoc, hπ', hπ], o'', ψ ≫ ψ'', mm, hTT, ?_⟩
    rw [hmm, hΦ, hΦ', Over.comp_left, Category.assoc, Category.assoc, ← Category.assoc φ.φ, ← hsq,
      Category.assoc]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PWitDeep
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pWitDeep :
    KNBasic → GenSm → TransDeep → WitComp → WitForget → WitDeep := by
  intro _ hSm hTD hWC hWF p _ D G L R _ _ gb X N' N h hI
  obtain ⟨k, hk, hAk, hex⟩ := hTD p D G L R gb h hI
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact absurd (Nat.coprime_zero_left _ |>.mp hk) (Fact.out : p.Prime).one_lt.ne'
    · exact hpos
  let Nk : Lv p := ⟨↑N * k, le_trans N.2.1 (Nat.le_mul_of_pos_right _ hk0), Nat.Coprime.mul N.2.2 hk⟩
  let M : Lv p := ⟨↑N' * (↑N * k), le_trans Nk.2.1 (Nat.le_mul_of_pos_left _ (by have := N'.2.1; omega)),
    Nat.Coprime.mul N'.2.2 Nk.2.2⟩
  have hNkM : (↑Nk : ℕ) ∣ ↑M := Dvd.intro_left _ rfl
  refine ⟨M, Dvd.intro _ rfl, ?_, ?_⟩
  · intro u hu
    exact hAk N u (UpperTheory.Gal.Int.Geo.KN_anti hNkM hu)
  · haveI : Smooth (X Nk).s := (hSm p D R gb Nk (X Nk)).1
    haveI : IsLocallyNoetherian (X Nk).X := LocallyOfFiniteType.isLocallyNoetherian (X Nk).s
    obtain ⟨o, ψ, ht⟩ := hex N (X Nk).X (X Nk).s (X Nk).univ
    obtain ⟨π, ⟨hπ, ⟨φ⟩⟩, -⟩ := (X N).rep (X Nk).X (X Nk).s o
    have w₂ : Wit L h (X Nk) (X N) π (ψ.left ≫ φ.φ) := ⟨hπ, o, ψ, φ, ht, rfl⟩
    obtain ⟨c, Φc, w₁, -⟩ := hWF p D G L R gb Nk M hNkM (X Nk) (X M)
    have := (hWC p D G L R gb M Nk N (X M) (X Nk) (X N) 1 h).2 hI (hAk N) c Φc π _ w₁ w₂
    rw [_root_.mul_one] at this
    exact ⟨_, _, this⟩
end


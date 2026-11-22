import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0003
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0047
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.GenericFiberGluing.SemistableCompleteSplit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0108
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0008

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsCoordPtFibre
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section

namespace GlobalTheory.FullExtend

open ThetaPtMove

theorem isCoordPt_move {S S' : Scheme.{0}} {f : S' ⟶ S} {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left)
    {P₀ : PolAV S} {P : PolAV S'} {φ : P.A.left ⟶ P₀.A.left}
    (hp : IsGrpPullback P.A P₀.A f φ) (hw : LBIso P.L (P₀.L.pull φ)) {B : Over S} (σ : T.left ⟶ B.left) [IsIso σ]
    (β : B ⟶ T₀) (hβ : σ ≫ β.left = τ) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
    (hg : ∀ th₀, IsGenSec P₀.A P₀.L 1 th₀ → IsGenSec P₀.A P₀.L 1 (VVRank.pullS P₀.A 1 β th₀))
    {k : ℕ} {I : Type} {x : I → (T ⟶ P.A)} {x₀ : I → (T₀ ⟶ P₀.A)} (hx : ∀ i, τ ≫ (x₀ i).left = (x i).left ≫ φ)
    (hk : ∀ i, x i ^ (k ^ 2) = 1) {z : T ⟶ P.A} {z₀ : T₀ ⟶ P₀.A} (hz : τ ≫ z₀.left = z.left ≫ φ)
    {v₀ : I → Γ(T₀.left, ⊤)} (H : IsCoordPt P₀ k x₀ z₀ v₀) :
    IsCoordPt P k x z (fun i => τ.appTop.hom (v₀ i)) := by
  obtain ⟨w, hw⟩ := hw
  have hL₀ := P₀.isLB
  have hL₁ := P.isLB
  have := P.isAb.comm
  obtain ⟨ho, hu, th₀, s₀, α₀, ρ₀, U₀, t₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := H
  obtain ⟨th, hth⟩ := exists_secRel hp τ hτ hw hL₀ hL₁ th₀
  obtain ⟨s, hs⟩ := exists_secRel hp τ hτ hw hL₀ hL₁ s₀
  choose t ht using fun i => exists_secRel hp τ hτ hw hL₀ hL₁ (t₀ i)
  obtain ⟨α, hα, vα⟩ := exists_genThrough₂ hp τ hτ hw hL₀ hL₁ (psi_pow hp τ hτ k) α₀ h₂
  obtain ⟨ρ, hρ, vρ⟩ := ConstFam.exists_gen_through (φ' := fun _ : Fin 1 => z.left) (h := τ) hw hL₀ hL₁
    (fun _ => hz.symm) ρ₀ h₃
  choose U hU hU' using fun i => symLift_move hp τ hτ hw hL₀ hL₁ (hx i) (hk i) (h₅ i)
  exact ⟨ho, (map_natCast τ.appTop.hom k) ▸ hu.map τ.appTop.hom, th, s, α, ρ, U, t,
    isGenSec_move hp τ hτ hw hL₀ hL₁ σ β hβ hth (hg _ h₁), hα, hρ,
    isTwistPull_move hp τ hτ hL₀ hL₁ (psi_pow hp τ hτ k) hα vα hth hs h₄, hU,
    fun i => hU' i _ _ _ _ hs (ht i) (h₆ i), fun i => isValueAt_move hp τ hτ hL₀ hL₁ hz vρ (ht i) (h₇ i)⟩

theorem isGenSec_base (hS : SecBaseChangeSt) {K : Type} [Field K] (P : PolAV (Sp K)) {R : Type} [CommRing R]
    (t : Sp R ⟶ (overRes (T := baseOver (Sp K)) ⊤).left) (th : LB.Sec (LPow P.A P.L 1 (baseOver (Sp K))))
    (h : IsGenSec P.A P.L 1 th) : IsGenSec P.A P.L 1 (VVRank.pullS P.A 1 (homAt t ≫ overResι ⊤) th) := by
  have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  obtain ⟨p₀⟩ : Nonempty (Sp K) := inferInstanceAs (Nonempty (PrimeSpectrum K))
  let i : baseOver (Sp K) ⟶ overRes (T := baseOver (Sp K)) ⊤ := Over.homMk (Sp K).topIso.inv
    ((congrArg (_ ≫ ·) (Category.comp_id _)).trans (Scheme.toIso_inv_ι _))
  have hi : overResι (T := baseOver (Sp K)) ⊤ ≫ i = 𝟙 _ := Over.OverMorphism.ext (Sp K).topIso.hom_inv_id
  have h₁ : IsGenSec P.A P.L 1 (VVRank.pullS P.A 1 (overResι ⊤) th) := fun s => by
    obtain ⟨r, hr⟩ := h (VVRank.pullS P.A 1 i s)
    have e : VVRank.pullM P.A P.L 1 i (SecM.ofSec P.A s) = r • SecM.ofSec P.A th := Subtype.ext (funext hr)
    have := congrArg (VVRank.pullM P.A P.L 1 (overResι ⊤)) e
    rw [VVRank.pullM_comp P.A P.isLB, hi, VVRank.pullM_id P.A P.isLB, LinearMap.map_smulₛₗ] at this
    exact ⟨_, fun j => congrArg (fun q => q.1 j) this⟩
  intro s
  obtain ⟨r, hr⟩ := isGenSec_pullS hS p₀ P t _ h₁ s
  have e := VVRank.pullM_comp P.A P.isLB 1 (homAt t) (overResι ⊤) (SecM.ofSec P.A th)
  exact ⟨r, fun j => (hr j).trans (congrArg (_ * ·) (congrArg (fun q => q.1 j) e))⟩

theorem isCoordPt_fibre (hS : SecBaseChangeSt) {K R : Type} [Field K] [CommRing R] {f : K →+* R} {P₀ : PolAV (Sp K)}
    {P : PolAV (Sp R)} {φ : P.A.left ⟶ P₀.A.left} (h : IsPolFibre f P₀ P φ) {k : ℕ} {I : Type}
    {x : I → (baseOver (Sp R) ⟶ P.A)} {x₀ : I → (baseOver (Sp K) ⟶ P₀.A)}
    (hx : ∀ i, spMap f ≫ (x₀ i).left = (x i).left ≫ φ) (hk : ∀ i, x i ^ (k ^ 2) = 1)
    {z : baseOver (Sp R) ⟶ P.A} {z₀ : baseOver (Sp K) ⟶ P₀.A} (hz : spMap f ≫ z₀.left = z.left ≫ φ)
    {v₀ : I → Γ(Sp K, ⊤)} (H : IsCoordPt P₀ k x₀ z₀ v₀) :
    IsCoordPt P k x z (fun i => (spMap f).appTop.hom (v₀ i)) := by
  let t : Sp R ⟶ (overRes (T := baseOver (Sp K)) ⊤).left := spMap f ≫ (Sp K).topIso.inv
  have ht : t ≫ (⊤ : (Sp K).Opens).ι = spMap f := by
    show (spMap f ≫ (Sp K).topIso.inv) ≫ _ = _
    rw [Category.assoc, Scheme.toIso_inv_ι, Category.comp_id]
  let σ : (baseOver (Sp R)).left ⟶ (baseAt t).left := 𝟙 (Sp R)
  have : IsIso σ := inferInstanceAs (IsIso (𝟙 (Sp R)))
  exact isCoordPt_move (T := baseOver (Sp R)) (T₀ := baseOver (Sp K)) (spMap f) h.2.1 h.2.2.symm σ
    (homAt t ≫ overResι ⊤) ((Category.id_comp _).trans ht) ((Category.comp_id _).trans (Category.id_comp _).symm)
    (isGenSec_base hS P₀ t) hx hk hz H

theorem prim_pull {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {L : LB G.left}
    {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB) (hw : LBIso (L.pull φ) L') {a : G ⟶ G} {a' : G' ⟶ G'}
    (ha : a'.left ≫ φ = φ ≫ a.left) (H : LBIso L (cubeLB G ![𝟙 G, a] L)) : LBIso L' (cubeLB G' ![𝟙 G', a'] L') := by
  have i₁ := pull_isLB hL φ
  have h₁ : LBIso (L.pull φ) (cubeLB G' ![𝟙 G', a'] (L.pull φ)) := by
    let U := pushPt h.1.w (𝟙 G')
    refine LBIso.chartPull (Geo.Tor.chartPullPull L _ U.left (Category.id_comp _))
      (chartPullLinComb L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) H
    fin_cases i
    · exact (Category.comp_id _).symm
    · exact Over.OverMorphism.ext (ha.trans (congrArg (· ≫ a.left) (Category.id_comp _).symm))
  obtain ⟨w, hw'⟩ := id hw
  exact LBIso.trans hL' (DVR.linComb_isLB _ i₁ _ _) (DVR.linComb_isLB _ hL' _ _)
    (LBIso.trans hL' i₁ (DVR.linComb_isLB _ i₁ _ _) hw.symm h₁) ⟨_, DVR.linCombIso_isGen w hw' _ _⟩

theorem exists_pointMap (hL : Laws) {K K' : Type} [Field K] [IsAlgClosed K] [CharZero K] [Field K'] [IsAlgClosed K']
    {f : K →+* K'} {P : PolAV (Sp K)} {P' : PolAV (Sp K')} {φ : P'.A.left ⟶ P.A.left} (h : IsPolFibre f P P' φ) :
    ∃ r : (baseOver (Sp K) ⟶ P.A) →* (baseOver (Sp K') ⟶ P'.A), (∀ x, (r x).left ≫ φ = spMap f ≫ x.left) ∧
      Function.Injective r ∧ (∀ n : ℕ, 0 < n → ∀ y, y ^ n = 1 → ∃ x, x ^ n = 1 ∧ r x = y) ∧
      ∀ (n : ℤ) x y (c : Kˣ), WeilIs P.A P.L n x y (unitOn c) →
        WeilIs P'.A P'.L n (r x) (r y) (unitOn (Units.map f.toMonoidHom c)) := by
  have := P'.isAb.comm
  obtain ⟨e, he⟩ := LiePull.exists_pushEquiv h.2.1 (baseOver (Sp K')) _ rfl
  let U : Over.mk ((baseOver (Sp K')).hom ≫ spMap f) ⟶ baseOver (Sp K) :=
    Over.homMk (spMap f) ((Category.comp_id _).trans (Category.id_comp _).symm)
  let r : (baseOver (Sp K) ⟶ P.A) →* (baseOver (Sp K') ⟶ P'.A) := e.symm.toMonoidHom.comp (preHom U)
  have hr : ∀ x, (r x).left ≫ φ = spMap f ≫ x.left := fun x =>
    (he _).symm.trans (congrArg (fun q => q.left) (e.apply_symm_apply (U ≫ x)))
  have inj : Function.Injective r := by
    letI := f.toAlgebra
    haveI : Flat (spMap f) := by
      rw [HasRingHomProperty.Spec_iff (P := @Flat)]
      exact (inferInstance : Module.Flat K K')
    haveI : Surjective (spMap f) := ⟨fun p => ⟨(⊥ : PrimeSpectrum K'), Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
    haveI : Epi (spMap f) := Flat.epi_of_flat_of_surjective (spMap f)
    exact fun x y E => Over.OverMorphism.ext ((cancel_epi (spMap f)).1
      ((hr x).symm.trans ((congrArg (fun q => q.left ≫ φ) E).trans (hr y))))
  refine ⟨r, hr, inj, fun n hn y hy => ?_, fun n x y c H => ?_⟩
  · have hk : (n : K) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    have hk' : (n : K') ≠ 0 := by rw [← map_natCast f]; exact (map_ne_zero f).2 hk
    have c₁ := (hL.mulN _ P n hn).2.2.2.2 K (𝟙 _) hk
    have c₂ := (hL.mulN _ P' n hn).2.2.2.2 K' (𝟙 _) hk'
    let F : {x : baseOver (Sp K) ⟶ P.A // x ^ n = 1} → {x : baseOver (Sp K') ⟶ P'.A // x ^ n = 1} :=
      fun x => ⟨r x.1, by rw [← map_pow, x.2, map_one]⟩
    have hF : Function.Injective F := fun a b E => Subtype.ext (inj (congrArg Subtype.val E))
    haveI : Finite {x : baseOver (Sp K') ⟶ P'.A // x ^ n = 1} :=
      Nat.finite_of_card_ne_zero (c₂.trans_ne (by positivity))
    obtain ⟨x, hx⟩ := (hF.bijective_of_nat_card_le (c₂.trans (by rw [h.1]; exact c₁.symm)).le).2 ⟨y, hy⟩
    exact ⟨x.1, x.2, congrArg Subtype.val hx⟩
  · have hu : Units.map U.left.appTop.hom.toMonoidHom (unitOn c) = unitOn (Units.map f.toMonoidHom c) :=
      Units.ext (congrArg (fun q => q.hom (c : K)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))).symm
    refine (weilIs_grpPullback_of_comm' _ _ _ _ _ _ _ _ P.isLB P'.isLB h.2.1 h.2.2.symm _ _ _ _ (U ≫ x) (U ≫ y) _
      (hr x).symm (hr y).symm).2 ?_
    exact hu ▸ CommPairing.weilIs_pull hL.globalFns P.isAb P.isLB U H

theorem fnOf_map {K K' : Type} [Field K] [Field K'] (f : K →+* K') (c : K) :
    fnOf (f c) = (spMap f).appTop.hom (fnOf c) :=
  congrArg (fun q => q.hom c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))

theorem exists_fullExt (hL : Laws) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {K K' : Type} [Field K] [IsAlgClosed K] [CharZero K] [Field K'] [IsAlgClosed K'] (f : K →+* K') (o : Full D K) :
    letI := H.starRing
    ∃ o' : Full D K', (o'.ρ = f o.ρ ∧ (∀ n, 0 < n → (o'.I.ζ n : K') = f (o.I.ζ n)) ∧
      ∃ φ : o'.P.A.left ⟶ o.P.A.left, IsGrpPullback o'.P.A o.P.A (spMap f) φ ∧ LBIso o'.P.L (o.P.L.pull φ) ∧
        (∀ x, (o'.oa.act x).left ≫ φ = φ ≫ (o.oa.act x).left) ∧
        ∀ n v, 0 < n → (o'.I.ev n v).left ≫ φ = spMap f ≫ (o.I.ev n v).left) ∧
      (∀ m v, o.Theta m v → o'.Theta m fun x => f (v x)) ∧
      ∀ m j z v, o.Coord m (o.I.ev j z) v → o'.Coord m (o'.I.ev j z) fun x => f (v x) := by
  letI := H.starRing
  obtain ⟨P', φ, hφ, hg, hm, hw⟩ := hL.polBaseChange _ _ (spMap f) o.P
  have hp : IsGrpPullback P'.A o.P.A (spMap f) φ := ⟨hφ, fun T x y x₀ y₀ hx hy => by
    obtain rfl : x₀ = toBase hφ.w x := Over.OverMorphism.ext hx
    obtain rfl : y₀ = toBase hφ.w y := Over.OverMorphism.ext hy
    exact congrArg (fun q => q.left) (hm T x y).symm⟩
  have h : IsPolFibre f o.P P' φ := ⟨hg, hp, hw⟩
  obtain ⟨oa, hoa⟩ := polOActPull _ _ _ o.P P' φ hp hw (𝓞 E) o.oa
  obtain ⟨r, hr, inj, onto, weil⟩ := exists_pointMap hL h
  have uinj : Function.Injective (Units.map f.toMonoidHom) := Units.map_injective f.injective
  have hact : ∀ c x, r (x ≫ o.oa.act c) = r x ≫ oa.act c := fun c x => Over.OverMorphism.ext (hφ.hom_ext (by
    rw [hr, Over.comp_left, Over.comp_left, Category.assoc, hoa, ← Category.assoc, ← Category.assoc, hr])
    (by rw [Over.w, Over.w]))
  have tors : ∀ m a, r (o.I.ev (m ^ 2) a) ^ (m ^ 2) = 1 := fun m a => by
    rcases Nat.eq_zero_or_pos (m ^ 2) with e | e
    · rw [e, pow_zero]
    · rw [← map_pow, (o.I.onto _ e _).2 ⟨a, rfl⟩, map_one]
  have det : DetCond D (ofRingAct oa.toRingAct) (𝟙 (Sp K')) (f o.ρ) := fun τ => by
    have q := (detCond_iff_of_field_extension E H D _ _ K K' f (𝟙 _) _ _ o.P.isAb.smooth).2 o.det τ
    have e := fun n => LiePull.lieMult_pull (𝓞 E) _ _ _ _ _ φ (ofRingAct o.oa.toRingAct) (ofRingAct oa.toRingAct) hp hoa
      K' (𝟙 _) τ n
    rw [e, e, Category.id_comp]
    rwa [Category.comp_id] at q
  refine ⟨{ P := P', oa := oa, prim := prim_pull hp o.P.isLB P'.isLB hw (hoa _) o.prim, ρ := f o.ρ
            ρ_sq := by rw [← map_pow, o.ρ_sq, map_neg, map_natCast]
            det := det
            closed := ‹_›
            I := { ζ := fun n => Units.map f.toMonoidHom (o.I.ζ n)
                   ζ_prim := fun n hn => (o.I.ζ_prim n hn).map_of_injective uinj
                   ζ_pow := fun n m hn hm => by rw [← map_pow, o.I.ζ_pow n m hn hm]
                   ev := fun n v => r (o.I.ev n v)
                   add := fun n a b => by rw [o.I.add, map_mul]
                   lin := fun n c a => by rw [o.I.lin, hact]
                   ker := fun n hn a => by rw [← o.I.ker n hn a, map_eq_one_iff r inj]
                   onto := fun n hn z => ⟨fun hz => ?_, ?_⟩
                   tower := fun n m hn hm a => by rw [← map_pow, o.I.tower n m hn hm]
                   isom := fun n hn a b => by rw [← map_zpow]; exact weil _ _ _ _ (o.I.isom n hn a b) } },
    ⟨rfl, fun _ _ => rfl, φ, hp, h.2.2.symm, hoa, fun n v _ => hr _⟩, fun m v Q => ?_, fun m j z v Q => ?_⟩
  · obtain ⟨y, hy, rfl⟩ := onto n hn z hz
    obtain ⟨a, rfl⟩ := (o.I.onto n hn y).1 hy
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    rw [← map_pow, (o.I.onto n hn _).2 ⟨a, rfl⟩, map_one]
  · have q := ConstThetaLevel.isThetaPt_fibre hL.secBaseChange h (fun a => (hr _).symm) (tors m) Q
    simp only [← fnOf_map] at q
    exact q
  · have q := isCoordPt_fibre hL.secBaseChange h (fun a => (hr _).symm) (tors m) (hr (o.I.ev j z)).symm Q
    simp only [← fnOf_map] at q
    exact q

end GlobalTheory.FullExtend

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSpreadsOutFromGenericFibreProper
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.GenSpread

set_option backward.isDefEq.respectTransparency false

theorem isLB_of_gm {Y : Scheme.{0}} (L : LB Y) (hc : ∀ y : Y, ∃ i, y ∈ L.U i)
    (h : ∀ (y : Y) i j k, y ∈ L.U i → y ∈ L.U j → y ∈ L.U k →
      gm (𝟙 Y) y _ (L.g i j) * gm (𝟙 Y) y _ (L.g j k) = gm (𝟙 Y) y _ (L.g i k)) : L.IsLB where
  cover := top_le_iff.1 fun y _ => Opens.mem_iSup.2 (hc y)
  g_self i := unit_ext fun y hy => by
    refine (gm_res (𝟙 Y) y _ hy _).trans ?_
    rw [map_one]
    exact mul_eq_left.1 (h y i i i hy hy hy)
  cocycle i j k := unit_ext fun y hy =>
    ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res (𝟙 Y) y _ hy _) (gm_res (𝟙 Y) y _ hy _))).trans
      ((h y i j k hy.1.1 hy.1.2 hy.2).trans (gm_res (𝟙 Y) y _ hy _).symm)

section Limit

variable {I : Type} [SmallCategory I] [IsCofiltered I]
  (D : I ⥤ Scheme.{0}) {X : Scheme.{0}} (π : ∀ i, X ⟶ D.obj i)
  (w : ∀ {i j} (f : i ⟶ j), π i ≫ D.map f = π j) (hc : IsLimit (schemeConeOfFamily D π w))
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]

include hc in

theorem exists_isLB_of_isLimit {i : I} [CompactSpace (D.obj i)] (M : LB (D.obj i)) [Finite M.ι]
    (hM : ∀ a b c, IsCompact ((M.U a ⊓ M.U b ⊓ M.U c : (D.obj i).Opens) : Set (D.obj i)))
    (hcov : ∀ y : X, ∃ a, π i y ∈ M.U a)
    (h : ∀ (y : X) a b c, π i y ∈ M.U a → π i y ∈ M.U b → π i y ∈ M.U c →
      gm (π i) y _ (M.g a b) * gm (π i) y _ (M.g b c) = gm (π i) y _ (M.g a c)) :
    ∃ (j : I) (f : j ⟶ i), (M.pull (D.map f)).IsLB := by
  have l₁ : ∀ a b c, M.U a ⊓ M.U b ⊓ M.U c ≤ M.U a ⊓ M.U b := fun a b c => inf_le_left
  have l₂ : ∀ a b c, M.U a ⊓ M.U b ⊓ M.U c ≤ M.U b ⊓ M.U c := fun a b c _ hy => ⟨hy.1.2, hy.2⟩
  have l₃ : ∀ a b c, M.U a ⊓ M.U b ⊓ M.U c ≤ M.U a ⊓ M.U c := fun a b c _ hy => ⟨hy.1.1, hy.2⟩
  have val : ∀ {Z : Scheme.{0}} (r : Z ⟶ D.obj i) (z : Z) a b c, r z ∈ M.U a ⊓ M.U b ⊓ M.U c →
      gm r z _ (res (l₁ a b c) (M.g a b) * res (l₂ a b c) (M.g b c)) =
        gm r z _ (M.g a b) * gm r z _ (M.g b c) := fun r z a b c hz =>
    (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hz _) (gm_res r z _ hz _))
  obtain ⟨j, f, hj⟩ := exists_common_refinement (i := i)
    (fun (p : M.ι × M.ι × M.ι) k g =>
      pullU (D.map g) _ (res (l₁ p.1 p.2.1 p.2.2) (M.g _ _) * res (l₂ p.1 p.2.1 p.2.2) (M.g _ _)) =
        pullU (D.map g) _ (res (l₃ p.1 p.2.1 p.2.2) (M.g _ _)))
    (by
      intro p k g k' g' h
      rw [D.map_comp]
      exact congrArg (pullU (D.map g') _) h)
    (by
      rintro ⟨a, b, c⟩
      exact exists_pullU_eq D π w hc (hM a b c) _ _ fun y hy =>
        (val (π i) y a b c hy).trans ((h y a b c hy.1.1 hy.1.2 hy.2).trans (gm_res _ y _ hy _).symm))
  obtain ⟨j', f', hj'⟩ := exists_map_preimage_le_map_preimage D _ hc (U := ⊤) (V := ⨆ a, M.U a)
    isCompact_univ (fun y _ => Opens.mem_iSup.2 (hcov y))
  obtain ⟨k, g, g', hg⟩ := IsCofiltered.cospan f f'
  refine ⟨k, g ≫ f, isLB_of_gm _ (fun y => ?_) fun y a b c ha hb hc' => ?_⟩
  · obtain ⟨a, ha⟩ := Opens.mem_iSup.1 (hj' (show D.map g' y ∈ D.map f' ⁻¹ᵁ ⊤ from trivial))
    refine ⟨fun _ => a, mem_pull.2 ?_⟩
    rw [hg, D.map_comp]
    exact ha
  · rw [gm_pull_g M _ (𝟙 _) y a b ha hb, gm_pull_g M _ (𝟙 _) y b c hb hc', gm_pull_g M _ (𝟙 _) y a c ha hc',
      Category.id_comp]
    have hy : D.map (g ≫ f) y ∈ M.U (a PUnit.unit) ⊓ M.U (b PUnit.unit) ⊓ M.U (c PUnit.unit) :=
      ⟨⟨mem_pull.1 ha, mem_pull.1 hb⟩, mem_pull.1 hc'⟩
    rw [D.map_comp] at hy ⊢
    have e := congrArg (gm (D.map g) y _) (hj (a PUnit.unit, b PUnit.unit, c PUnit.unit))
    exact (val _ y _ _ _ hy).symm.trans ((gm_pull (D.map g) (D.map f) y _ hy _).symm.trans (e.trans
      ((gm_pull (D.map g) (D.map f) y _ hy _).trans (gm_res _ y _ hy _))))

include hc in

theorem exists_lb_of_isLimit {i : I} [CompactSpace (D.obj i)] [CompactSpace X]
    (hsep : ∀ U V : (D.obj i).Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V))
    (hπ : Topology.IsInducing (π i)) (L₀ : LB X) (hL : L₀.IsLB) :
    ∃ (j : I) (L : LB (D.obj j)), L.IsLB ∧ LBIso L₀ (L.pull (π j)) := by
  have loc : ∀ x : X, ∃ (V : (D.obj i).Opens) (c : L₀.ι),
      IsAffineOpen V ∧ π i x ∈ V ∧ π i ⁻¹ᵁ V ≤ L₀.U c := by
    intro x
    obtain ⟨c, hc⟩ := exists_chart hL x
    obtain ⟨W, hW, hW'⟩ := hπ.isOpen_iff.1 (L₀.U c).isOpen
    have hx : π i x ∈ W := hW'.ge hc
    obtain ⟨_, ⟨V, hV, rfl⟩, hx, hle⟩ := (D.obj i).isBasis_affineOpens.exists_subset_of_mem_open hx hW
    exact ⟨V, c, hV, hx, fun y hy => hW'.le (hle hy)⟩
  choose V c hV hx hle using loc
  obtain ⟨σ, hσ⟩ := CompactSpace.elim_nhds_subcover (fun x => ((π i ⁻¹ᵁ V x : X.Opens) : Set X))
    (fun x => (π i ⁻¹ᵁ V x).isOpen.mem_nhds (hx x))
  have cov : ∀ x : X, ∃ a : σ, π i x ∈ V a := fun x => by
    obtain ⟨a, ha, hx⟩ := Set.mem_iUnion₂.1 (hσ.ge (Set.mem_univ x))
    exact ⟨⟨a, ha⟩, hx⟩
  have le : ∀ {j k : I} (f : j ⟶ i) (g : k ⟶ j) (U : (D.obj i).Opens),
      D.map (g ≫ f) ⁻¹ᵁ U ≤ D.map g ⁻¹ᵁ (D.map f ⁻¹ᵁ U) := fun f g U => by
    rw [D.map_comp, Scheme.Hom.comp_preimage]
  have l : ∀ a b, π i ⁻¹ᵁ (V a ⊓ V b) ≤ L₀.U (c a) ⊓ L₀.U (c b) := fun a b _ hy => ⟨hle a hy.1, hle b hy.2⟩
  obtain ⟨j, f, hj⟩ := exists_common_refinement (i := i)
    (fun (p : σ × σ) j f => ∃ t : Γ(D.obj j, D.map f ⁻¹ᵁ (V p.1 ⊓ V p.2))ˣ, ∀ y : X,
      y ∈ π i ⁻¹ᵁ (V p.1 ⊓ V p.2) →
      gm (π j) y (D.map f ⁻¹ᵁ (V p.1 ⊓ V p.2)) t = gm (𝟙 X) y _ (res (l p.1 p.2) (L₀.g _ _)))
    (by
      rintro p j f k g ⟨t, ht⟩
      refine ⟨res (le f g _) (pullU (D.map g) _ t), fun y hy => ?_⟩
      have hy' := cone_preimage_le D π w (g ≫ f) _ hy
      refine (gm_res_pullU (π k) (D.map g) y (le f g (V p.1 ⊓ V p.2)) hy' t).trans ?_
      rw [w g]
      exact ht y hy)
    (fun p => exists_unit_π_eq D π w hc (hsep _ _ (hV _) (hV _)) _)
  choose t ht using hj
  let M : LB (D.obj j) := ⟨σ, fun a => D.map f ⁻¹ᵁ V a, fun a b => t (a, b)⟩
  have mem : ∀ (y : X) (a : σ), π j y ∈ M.U a ↔ π i y ∈ V a := fun y a => by
    rw [← w f]; rfl
  have val : ∀ (y : X) (a b : σ), π j y ∈ M.U a → π j y ∈ M.U b →
      gm (π j) y _ (M.g a b) = gm (𝟙 X) y _ (L₀.g (c a) (c b)) := fun y a b ha hb =>
    have hy : y ∈ π i ⁻¹ᵁ (V a ⊓ V b) := ⟨(mem y a).1 ha, (mem y b).1 hb⟩
    (ht (a, b) y hy).trans (gm_res _ y _ hy _)
  have : CompactSpace (D.obj j) := QuasiCompact.compactSpace_of_compactSpace (D.map f)
  have : Finite M.ι := inferInstanceAs (Finite σ)
  obtain ⟨k, g, hk⟩ := exists_isLB_of_isLimit D π w hc M
    (fun a b e => ((hsep _ _ (hsep _ _ (hV a) (hV b)) (hV e)).preimage (D.map f)).isCompact)
    (fun y => (cov y).imp fun a ha => (mem y a).2 ha)
    (fun y a b e ha hb he => by
      rw [val y a b ha hb, val y b e hb he, val y a e ha he]
      exact gm_cocycle hL (𝟙 X) y (hle a ((mem y a).1 ha)) (hle b ((mem y b).1 hb)) (hle e ((mem y e).1 he)))
  have mem' : ∀ (y : X) J, y ∈ ((M.pull (D.map g)).pull (π k)).U J → π j y ∈ M.U (J PUnit.unit PUnit.unit) :=
    fun y J hy => by
      rw [← w g]
      have hy' : π k y ∈ (M.pull (D.map g)).U (J PUnit.unit) := mem_pull.1 hy
      exact (mem_pull (F := D.map g)).1 hy'
  refine ⟨k, _, hk, (lbIso_of_chartPull (B' := (M.pull (D.map g)).pull (π k))
    ⟨fun J => c (J PUnit.unit PUnit.unit).1, fun J y hy => hle _ ((mem y _).1 (mem' y J hy)),
      fun y J J' hJ hJ' => ?_⟩ hL).symm⟩
  rw [gm_pull_g _ _ (𝟙 _) y J J' hJ hJ', Category.id_comp,
    gm_pull_g M _ (π k) y _ _ (mem_pull.1 hJ) (mem_pull.1 hJ'), w g]
  exact val y _ _ (mem' y J hJ) (mem' y J' hJ')

end Limit

theorem exists_lb {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    {X X₀ : Scheme.{0}} (f : X ⟶ Sp R) [QuasiCompact f] [IsSeparated f] {φ : X₀ ⟶ X} {f₀ : X₀ ⟶ Sp K}
    (h : IsPullback φ f₀ f (spMap (algebraMap R K))) {L₀ : LB X₀} (hL : L₀.IsLB) :
    ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) →
      ∀ (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Sp R'), π ≫ f = f' ≫ spMap g →
        ∃ L' : LB X', L'.IsLB ∧ ∀ φ' : X₀ ⟶ X', φ' ≫ π = φ → LBIso L₀ (L'.pull φ') := by
  obtain ⟨p₁, h₁⟩ := exists_isPullback_stalk h
  obtain ⟨hc⟩ := StalkLimit.nonempty_isLimit h₁
  obtain ⟨V₀⟩ : Nonempty (StalkLimit.AffNhd (genericPoint (Sp R))) := IsCofiltered.nonempty
  have : IsAffine V₀.1.toScheme := V₀.2.2
  have : CompactSpace ((StalkLimit.diagram _ f).obj V₀) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f V₀.1.ι)
  have : QuasiCompact f₀ := MorphismProperty.of_isPullback (P := @QuasiCompact) h inferInstance
  have : CompactSpace X₀ := QuasiCompact.compactSpace_of_compactSpace f₀
  have : IsPreimmersion φ := MorphismProperty.of_isPullback (P := @IsPreimmersion) h₁.flip inferInstance
  have hs : (pullback f V₀.1.ι).IsSeparated :=
    ⟨by rw [← terminal.comp_from (pullback.snd f V₀.1.ι)]; infer_instance⟩
  have : ((StalkLimit.diagram _ f).obj V₀).IsSeparated := hs
  have hi : Topology.IsInducing ((StalkLimit.cone h₁).π.app V₀) := by
    refine Topology.IsInducing.of_comp (g := pullback.fst f V₀.1.ι) (Scheme.Hom.continuous _)
      (Scheme.Hom.continuous _) ?_
    have := φ.isEmbedding.isInducing
    rw [← StalkLimit.cone_π_fst h₁ V₀] at this
    exact this
  obtain ⟨V, L, hL', H⟩ := exists_lb_of_isLimit (StalkLimit.diagram _ f) (fun V => (StalkLimit.cone h₁).π.app V)
    (fun i => (StalkLimit.cone h₁).w i) hc (i := V₀) (fun U W hU hW => hU.inf hW) hi L₀ hL
  obtain ⟨a, ha, Ha⟩ := exists_forall_mem V.2.1
  refine ⟨a, ha, fun R' _ g hg X' π f' e => ?_⟩
  obtain ⟨l, hl⟩ := exists_lift_open f V.1 e (Ha R' g hg)
  refine ⟨L.pull l, pull_isLB hL' _, fun φ' hφ' => ?_⟩
  have : (StalkLimit.cone h₁).π.app V = φ' ≫ l := by
    rw [← cancel_mono (pullback.fst f V.1.ι), Category.assoc, hl, hφ', StalkLimit.cone_π_fst]
  exact LBIso.trans hL (pull_isLB hL' _) (pull_isLB (pull_isLB hL' _) _) H (lbIso_pull_pull hL' φ' this)

theorem lineBundle_spreads_out (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (X X₀ : Scheme.{0}) (f : X ⟶ Sp R) (f₀ : X₀ ⟶ Sp K) (φ : X₀ ⟶ X)
    (h : IsPullback φ f₀ f (spMap (algebraMap R K))) (_ : Flat f) (_ : IsProper f) (L₀ : LB X₀) (hL : L₀.IsLB) :
    ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) →
      ∀ (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Sp R'), π ≫ f = f' ≫ spMap g →
        ∃ L' : LB X', L'.IsLB ∧ ∀ φ' : X₀ ⟶ X', φ' ≫ π = φ → LBIso L₀ (L'.pull φ') :=
  exists_lb f h hL

end GlobalTheory.GenSpread
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NumberFieldStandardFacts
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem geometricallyConnected_of_generic_of_special (W L : Type) [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] {X : Scheme.{0}} (f : X ⟶ Sp W)
    (h₁ : GeometricallyConnected (pullback.snd f (spMap (algebraMap W L))))
    (h₂ : GeometricallyConnected (pullback.snd f (spMap (algebraMap W (IsLocalRing.ResidueField W))))) :
    GeometricallyConnected f := by
  have key : ∀ (Ω F : Type) [Field Ω] [Field F] (a : W →+* F) (ψ : F →+* Ω),
      GeometricallyConnected (pullback.snd f (spMap a)) →
      ∀ (Z : Scheme.{0}) (fst : Z ⟶ X) (snd : Z ⟶ Sp Ω), IsPullback fst snd f (spMap (ψ.comp a)) →
      ConnectedSpace Z := by
    intro Ω F _ _ a ψ h Z fst snd hZ
    have e : spMap (ψ.comp a) = spMap ψ ≫ spMap a := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [e] at hZ
    have sq : IsPullback (pullback.lift fst (snd ≫ spMap ψ) (hZ.w.trans (Category.assoc _ _ _).symm)) snd
        (pullback.snd f (spMap a)) (spMap ψ) :=
      IsPullback.of_right (by rw [pullback.lift_fst]; exact hZ) (pullback.lift_snd _ _ _)
        (IsPullback.of_hasPullback f (spMap a))
    exact GeometricallyConnected.geometrically_connectedSpace (f := pullback.snd f (spMap a)) _ _ _ sq
  refine ⟨fun Ω _ q Z fst snd hZ => ?_⟩
  obtain ⟨φ, rfl⟩ := Spec.map_surjective q
  change IsPullback fst snd f (spMap φ.hom) at hZ
  by_cases h : RingHom.ker φ.hom = ⊥
  · have hinj := (RingHom.injective_iff_ker_eq_bot _).2 h
    have e : (IsFractionRing.lift (K := L) hinj).comp (algebraMap W L) = φ.hom :=
      RingHom.ext fun x => IsFractionRing.lift_algebraMap hinj x
    rw [← e] at hZ
    exact key Ω L _ _ h₁ Z fst snd hZ
  · have hm : RingHom.ker φ.hom = IsLocalRing.maximalIdeal W :=
      IsLocalRing.eq_maximalIdeal ((RingHom.ker_isPrime φ.hom).isMaximal h)
    let ψ : IsLocalRing.ResidueField W →+* Ω :=
      Ideal.Quotient.lift (IsLocalRing.maximalIdeal W) φ.hom fun a ha => (RingHom.mem_ker).1 (hm ▸ ha)
    have e : ψ.comp (algebraMap W (IsLocalRing.ResidueField W)) = φ.hom := RingHom.ext fun x => rfl
    rw [← e] at hZ
    exact key Ω _ _ _ h₂ Z fst snd hZ

theorem isSemiAbelian_of_abelian_generic_of_torusExt : NfSt := by
  intro W _ _ _ L _ _ _ A _ hA G _ hc hs hsep hqc ⟨e, _⟩ hT
  obtain ⟨k, _, _, _, ⟨E⟩⟩ := GlobalTheory.T.exists_finite_splitTorusExtension_of_torusExtension _ _ hT
  have hw : (baseChange W L G).hom = e.hom.left ≫ A.hom := (Over.w e.hom).symm
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have := hA.proper
  have := hA.geomConnected
  have hp : IsProper (baseChange W L G).hom := by rw [hw]; infer_instance
  have hg : GeometricallyConnected (baseChange W L G).hom :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      (IsPullback.of_horiz_isIso (fst := e.hom.left) (g := 𝟙 _) ⟨by rw [hw, Category.comp_id]⟩) hA.geomConnected
  have hk := (GlobalTheory.torusExtension_smooth_geometricallyConnected _ E).2.2.2.1
  have hsurj : Surjective (spMap (algebraMap (IsLocalRing.ResidueField W) k)) :=
    ⟨fun z => ⟨_, Subsingleton.elim (spMap (algebraMap (IsLocalRing.ResidueField W) k)
      (default : PrimeSpectrum _)) z⟩⟩
  have hsp : GeometricallyConnected (specialFibre W G).hom :=
    @GlobalTheory.geometricallyConnected_of_isPullback_of_surjective _ _ _ _ _ _ _ _
      (IsPullback.of_hasPullback (specialFibre W G).hom (spMap (algebraMap (IsLocalRing.ResidueField W) k)))
      hsurj hk
  have hgc : GeometricallyConnected G.hom := geometricallyConnected_of_generic_of_special W L G.hom hg hsp
  refine isSemiAbelian_of_proper_generic_of_torusExtension W L G ⟨hc, hs, hsep, hqc, hgc⟩ hp k
    ((algebraMap (IsLocalRing.ResidueField W) k).comp (algebraMap W (IsLocalRing.ResidueField W))) ?_ ?_ ?_
  · rw [RingHom.ker_comp_of_injective _ (algebraMap (IsLocalRing.ResidueField W) k).injective]
    exact IsLocalRing.ker_residue
  · refine RingHom.IsIntegral.trans _ _ (RingHom.isIntegral_of_surjective _ IsLocalRing.residue_surjective) ?_
    exact Algebra.IsIntegral.isIntegral
  · have e' : spMap ((algebraMap (IsLocalRing.ResidueField W) k).comp (algebraMap W (IsLocalRing.ResidueField W))) =
        spMap (algebraMap (IsLocalRing.ResidueField W) k) ≫ spMap (algebraMap W (IsLocalRing.ResidueField W)) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [e']
    have : IsMonHom (pullCompIso (spMap (algebraMap (IsLocalRing.ResidueField W) k))
        (spMap (algebraMap W (IsLocalRing.ResidueField W))) G).symm.hom :=
      inferInstanceAs (IsMonHom (pullCompIso _ _ G).inv)
    exact ⟨torusExtOfIso (pullCompIso (spMap (algebraMap (IsLocalRing.ResidueField W) k))
        (spMap (algebraMap W (IsLocalRing.ResidueField W))) G).symm E⟩

end GlobalTheory.SS
end


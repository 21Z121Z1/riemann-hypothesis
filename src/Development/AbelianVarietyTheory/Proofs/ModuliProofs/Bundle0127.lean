import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0056
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0106
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0117
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0089
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSimTrivialOfMult
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0063
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.AppLESurjective
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionSectionCoordsThetaTimesRoots
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0121
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsVeryAmpleSectionSystemOfProjectiveCoordinates
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZV

noncomputable section
namespace GlobalTheory.ZV.CoordEmbed
open GlobalTheory.ZM.RepBC

theorem appLE_bijective {X Y : Scheme.{0}} (x : Y ⟶ X) [IsOpenImmersion x] {V : X.Opens} {W : Y.Opens}
    (hV : V ≤ x.opensRange) (e : W ≤ x ⁻¹ᵁ V) (e' : x ⁻¹ᵁ V ≤ W) :
    Function.Bijective (x.appLE V W e).hom := by
  obtain rfl : W = x ⁻¹ᵁ V := le_antisymm e e'
  have hiso : IsIso (x.app V) := x.isIso_app V hV
  rw [← x.app_eq_appLE]
  first
    | exact (asIso (x.app V)).commRingCatIsoToRingEquiv.bijective

theorem cover {K σ : Type} [CommRing K] {I : Ideal (MvPolynomial σ K)} {Z : Scheme.{0}} {p : Z ⟶ Sp K} {M : LB Z}
    {th : σ → M.Sec} (h : ProjRep I p M th) : ⨆ i, Out.nonzeroLocus (th i) = ⊤ := by
  obtain ⟨hLB, hpt, -⟩ := h
  rw [eq_top_iff]
  rintro z -
  obtain ⟨R, _, x, v, -, ⟨q, rfl⟩, hv⟩ := (GlobalTheory.T.sectionCoordinateVector_exists_locally Z M σ th hLB).2.2 z
  have hβ : x ≫ p = spMap (Spec.preimage (x ≫ p)).hom := by
    unfold spMap
    simp
  have hspan := (hpt R _ x v hβ hv).1
  obtain ⟨i, hi⟩ : ∃ i, v i ∉ q.asIdeal := by
    by_contra hno
    simp only [not_exists, not_not] at hno
    apply q.isPrime.ne_top
    rw [eq_top_iff, ← hspan, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hno i
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, ((GlobalTheory.T.sectionCoordinates_pull_iso_nonzeroLocus Z M σ th hLB).2.2 R x v i q hv).2 hi⟩

theorem ratios {K σ S : Type} [CommRing K] [CommRing S] {Z : Scheme.{0}} {p : Z ⟶ Sp K} {M : LB Z}
    {th : σ → M.Sec} (i : σ) (D : Z.Opens) (x : Sp S ⟶ Z) [IsOpenImmersion x] (hD : x.opensRange = D)
    (β : K →+* S) (hx : x ≫ p = spMap β) (v : σ → S) (hv : SecCoord M th x v) (hi : v i = 1)
    (hgen : ∀ a : S, ∃ F : MvPolynomial σ K, a = MvPolynomial.eval₂ β v F) :
    ∃ r : σ → Γ(Z, D),
      (∀ j k, resG Z (inf_le_right : D ⊓ M.U k ≤ M.U k) ((th j).f k) =
        resG Z (inf_le_left : D ⊓ M.U k ≤ D) (r j) * resG Z (inf_le_right : D ⊓ M.U k ≤ M.U k) ((th i).f k)) ∧
      ∀ f : Γ(Z, D), ∃ F : MvPolynomial σ K,
        f = MvPolynomial.eval₂ (RingHom.comp (p.appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) r F := by
  obtain ⟨τ, -, hvτ⟩ := hv
  have hU : ∀ k, (M.pull x).U (fun _ => k) = x ⁻¹ᵁ M.U k := fun k => by
    ext1
    simp only [LB.pull, LB.LinComb, LB.wchart, Scheme.Hom.coe_preimage]
    first
      | exact Set.iInter_const _
      | simp
  have hxD : x ⁻¹ᵁ D = ⊤ := by
    rw [← hD]
    exact Scheme.Hom.preimage_opensRange x
  have hDle : D ≤ x.opensRange := hD.ge

  have hres : ∀ (A B : Z.Opens) (hAB : A ≤ B) (W : (Sp S).Opens) (hW : W ≤ x ⁻¹ᵁ A) (a : Γ(Z, B)),
      (x.appLE A W hW).hom (resG Z hAB a) = (x.appLE B W (hW.trans fun _ hz => hAB hz)).hom a := by
    intro A B hAB W hW a
    unfold resG
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

  have hres' : ∀ (A : Z.Opens) (W W' : (Sp S).Opens) (hW : W ≤ x ⁻¹ᵁ A) (hW' : W' ≤ W) (a : Γ(Z, A)),
      resG (Sp S) hW' ((x.appLE A W hW).hom a) = (x.appLE A W' (hW'.trans hW)).hom a := by
    intro A W W' hW hW' a
    unfold resG
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  have hcomp : ∀ (W₁ W₂ W₃ : (Sp S).Opens) (h₁ : W₂ ≤ W₁) (h₂ : W₃ ≤ W₂) (a : Γ(Sp S, W₁)),
      resG (Sp S) h₂ (resG (Sp S) h₁ a) = resG (Sp S) (h₂.trans h₁) a := by
    intro W₁ W₂ W₃ h₁ h₂ a
    unfold resG
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  have hbij := appLE_bijective x hDle hxD.ge le_top

  obtain ⟨r, hr⟩ : ∃ r : σ → Γ(Z, D),
      ∀ j, (x.appLE D ⊤ hxD.ge).hom (r j) = (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (v j) :=
    ⟨fun j => (hbij.2 _).choose, fun j => (hbij.2 _).choose_spec⟩
  refine ⟨r, fun j k => ?_, fun f => ?_⟩
  · have hk : x ⁻¹ᵁ (D ⊓ M.U k) ≤ (M.pull x).U (fun _ => k) := by
      rw [hU]
      exact fun _ hz => hz.2
    have key : ∀ (l : σ) (h' : x ⁻¹ᵁ (D ⊓ M.U k) ≤ x ⁻¹ᵁ M.U k),
        (x.appLE (M.U k) (x ⁻¹ᵁ (D ⊓ M.U k)) h').hom ((th l).f k) =
          resG (Sp S) hk (resG (Sp S) (le_top : (M.pull x).U (fun _ => k) ≤ ⊤)
            ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (v l)) *
            ((τ.s fun _ => k).val : Γ(Sp S, (M.pull x).U fun _ => k))) := by
      intro l h'
      rw [← hvτ l (fun _ => k) (hU k).le, hres']
    have hrj : ∀ (h' : x ⁻¹ᵁ (D ⊓ M.U k) ≤ x ⁻¹ᵁ D),
        (x.appLE D (x ⁻¹ᵁ (D ⊓ M.U k)) h').hom (r j) =
          resG (Sp S) le_top ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (v j)) := by
      intro h'
      rw [← hr j, hres']
    apply (appLE_bijective x (inf_le_left.trans hDle) le_rfl le_rfl).1
    rw [map_mul, hres, hres, hres, key j, key i, hrj, hi]
    simp only [map_one, _root_.one_mul, map_mul, hcomp]
  · obtain ⟨F, hF⟩ := hgen ((Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom ((x.appLE D ⊤ hxD.ge).hom f))
    refine ⟨F, hbij.1 ?_⟩
    have hbase : ∀ (g : Sp S ⟶ Sp K) (hg : g = spMap β) (e : (⊤ : (Sp S).Opens) ≤ g ⁻¹ᵁ ⊤) (c : K),
        (g.appLE ⊤ ⊤ e).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c) =
          (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (β c) := by
      rintro g rfl e c
      exact GlobalTheory.ZM.Coord.appLE_spec β e c
    have h₁ : (x.appLE D ⊤ hxD.ge).hom.comp
        (RingHom.comp (p.appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) =
        (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom.comp β := by
      ext c
      show (x.appLE D ⊤ hxD.ge).hom ((p.appLE ⊤ D le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c)) =
        (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (β c)
      have hcc := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c))
        (Scheme.Hom.appLE_comp_appLE x p ⊤ D ⊤ le_top hxD.ge)
      exact hcc.trans (hbase _ hx _ c)
    have h₂ : (x.appLE D ⊤ hxD.ge).hom ∘ r = (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom ∘ v := funext hr
    rw [MvPolynomial.eval₂_comp_left, h₁, h₂, ← MvPolynomial.eval₂_comp_left, ← hF,
      ← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]

theorem vAmp_of_projRep : ∀ (K σ : Type) [Field K] [Finite σ] (I : Ideal (MvPolynomial σ K)) (Z : Scheme.{0}) (p : Z ⟶ Sp K) (M : LB Z) (th : σ → M.Sec), ProjRep I p M th → VAmp p M th := by
  intro K σ _ _ I Z p M th h
  refine ⟨cover h, fun i => ?_⟩
  obtain ⟨x, hx, hrange, hxs, hsc⟩ := GlobalTheory.T.exists_nonzeroCoordinate_affineChart K σ I Z p M th i h
  have hD : x.opensRange = Out.nonzeroLocus (th i) := TopologicalSpace.Opens.ext hrange
  refine ⟨hD ▸ isAffineOpen_opensRange x, ?_⟩
  refine ratios i _ x hD _ hxs _ hsc ?_ ?_
  · rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
    exact Ideal.mem_sup_right (Ideal.subset_span rfl)
  · intro a
    obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective a
    refine ⟨F, ?_⟩
    conv_lhs => rw [← MvPolynomial.eval₂_eta F]
    exact MvPolynomial.eval₂_comp_left _ _ _ _

end GlobalTheory.ZV.CoordEmbed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjectiveOfLaws
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.LevelCover

namespace GlobalTheory.LevCover

private theorem levStrRep_lemma (hL : Out.Laws) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {D : Datum H} {l : Level H} {B : Type} [Field B] {b : Base l B} {S : Scheme.{0}} [IsLocallyNoetherian S]
    {s : S ⟶ Sp B} (o : Obj D l b s) (hpq : 1 ≤ D.p + D.q) (l₂ : Level H) (b₂ : Base l₂ B) (hd : l.Dvd l₂)
    (hζ : b.ζ = b₂.ζ ^ (l₂.A / l.A)) :
    ∃ (V : Over S) (χ θ : D.La → (V ⟶ o.t.G)), IsFinite V.hom ∧ Etale V.hom ∧ Surjective V.hom ∧
      LevStr o b₂ V χ θ ∧
      (∀ (T : Over S) (u u' : T ⟶ V), (∀ a, u ≫ χ a = u' ≫ χ a) → (∀ a, u ≫ θ a = u' ≫ θ a) → u = u') ∧
      ∀ (T : Over S) (χ' θ' : D.La → (T ⟶ o.t.G)), LevStr o b₂ T χ' θ' →
        ∃ h : T ⟶ V, (∀ a, h ≫ χ a = χ' a) ∧ ∀ a, h ≫ θ a = θ' a := by
  have hsim := SimAlg.sim_group E H D hpq
  obtain ⟨hfree, hfin⟩ := datum_free D
  refine exists_levStr_rep o l₂ b₂ hd hζ (fun g n k hn hk => hsim.1 g n k hn hk)
    (fun N f ν => exists_sim_lift E H D N f ν)
    (fun l' N ν => SimMult.exists_sim_trivial_of_mult SimAlg.sim_group exists_sim_lift E H D l' N ν) ?_ ?_
  · intro n hn
    have hu : IsUnit ((n : ℕ) : Γ(S, ⊤)) := by
      simpa using (b.unit n hn).map (fnOn s)
    obtain ⟨Z, et, hZ⟩ :=
      exists_finiteEtale_latticeTorsionHom S o.t.G n D.La (ObjDim.isAbelianScheme o) hu
    exact ⟨Z, et, hZ⟩
  · intro N _ T x y c hN hx hy hc
    exact PairingLocus.exists_clopen_of_isLocallyNoetherian hL S (GlobalTheory.Obj.toPolAV o) N T x y c hN hx hy hc

private theorem weilIs_iff_of_sabMap {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) (T' : Over S') (k : ℤ) (x y : T' ⟶ t'.G)
    (x₀ y₀ : Over.mk (T'.hom ≫ f) ⟶ t.G) (c : Γ(T'.left, ⊤)ˣ) (h₁ : x₀.left = x.left ≫ m.φ)
    (h₂ : y₀.left = y.left ≫ m.φ) : Out.WeilIs t'.G t'.PP.L k x y c ↔ Out.WeilIs t.G t.PP.L k x₀ y₀ c :=
  weilIs_grpPullback_of_comm S S' t.G t'.G f m.φ t.PP.L t'.PP.L t.PP.isLB t'.PP.isLB m.cart (sabMap_lbIso m)
    T' k x y x₀ y₀ c h₁ h₂

private theorem lieMult_iff_of_sabMap {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) (k : Type) [Field k] (x : Sp k ⟶ S')
    (τ : 𝓞 E →+* k) (n : ℕ) : LieMult t'.act x τ n ↔ LieMult t.act (x ≫ f) τ n :=
  LiePull.lieMult_pull (𝓞 E) S S' t.G t'.G f m.φ t.act t'.act m.cart m.act k x τ n

theorem levelCover_noetherian (hL : Out.Laws) : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (B : Type) [Field B] (b : Base l B) (b₂ : Base l₂ B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsLocallyNoetherian S → 1 ≤ D.p + D.q → l.Dvd l₂ → b.ρ = b₂.ρ → b.ζ = b₂.ζ ^ (l₂.A / l.A) → ∃ (S₂ : Scheme.{0}) (π : S₂ ⟶ S) (o₂ : Obj D l₂ b₂ (π ≫ s)) (m : SABMap o₂.t o.t π), IsFinite π ∧ Etale π ∧ Surjective π ∧ ((∀ a, (o₂.eta a ^ (l₂.M / l.M)).left ≫ m.φ = π ≫ (o.eta a).left) ∧ (∀ a, (o₂.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = π ≫ (o.etaA a).left)) ∧ ∀ (T : Scheme.{0}) (f : T ⟶ S) (o' : Obj D l₂ b₂ (f ≫ s)) (m' : SABMap o'.t o.t f), (∀ a, (o'.eta a ^ (l₂.M / l.M)).left ≫ m'.φ = f ≫ (o.eta a).left) ∧ (∀ a, (o'.etaA a ^ (l₂.A / l.A)).left ≫ m'.φ = f ≫ (o.etaA a).left) → ∃! h : T ⟶ S₂, h ≫ π = f ∧ ∃ u : ObjMap o' o₂ h, u.toSABMap.φ ≫ m.φ = m'.φ := by
  intro E _ _ _ H D l l₂ B _ b b₂ S s o hS hpq hd hρ hζ
  have := hS
  obtain ⟨V, χ, θ, hVf, hVe, hVs, hlev, hext, hex⟩ := levStrRep_lemma hL o hpq l₂ b₂ hd hζ
  obtain ⟨o₁, ⟨n₁⟩⟩ := obj_pull E H D l B B b b (RingHom.id B) S V.left s (V.hom ≫ s) V.hom rfl rfl
    (by rw [spMap_id', Category.comp_id]) o
  obtain ⟨o₂, m, hm, hχ, hθ⟩ := obj_of_levStr o hρ V o₁.t n₁.toSABMap (weilIs_iff_of_sabMap n₁.toSABMap)
    (fun k _ x τ n => lieMult_iff_of_sabMap n₁.toSABMap k x τ n) o₁.ample o₁.ktriv hlev
  refine ⟨V.left, V.hom, o₂, m, hVf, hVe, hVs, hm, ?_⟩
  intro T f o' m' hc
  obtain ⟨χ', θ', hlev', hχ', hθ'⟩ := levStr_of_obj o (Over.mk f) o' m' (weilIs_iff_of_sabMap m') hc.1 hc.2
  obtain ⟨g, hgχ, hgθ⟩ := hex (Over.mk f) χ' θ' hlev'
  have hg : g.left ≫ V.hom = f := by simpa using Over.w g
  obtain ⟨u, hu⟩ := sab_cancel m m' g.left hg

  have key : ∀ a, ((o'.eta a).left ≫ m'.φ = g.left ≫ (o₂.eta a).left ≫ m.φ) ∧
      ((o'.etaA a).left ≫ m'.φ = g.left ≫ (o₂.etaA a).left ≫ m.φ) := fun a => by
    constructor
    · rw [← hχ' a, ← hgχ a, Over.comp_left, hχ a]
    · rw [← hθ' a, ← hgθ a, Over.comp_left, hθ a]
  have hη : ∀ a, (o'.eta a).left ≫ u.φ = g.left ≫ (o₂.eta a).left := fun a =>
    sec_cancel u m (o'.eta a) (o₂.eta a) (by rw [hu]; exact (key a).1)
  have hηA : ∀ a, (o'.etaA a).left ≫ u.φ = g.left ≫ (o₂.etaA a).left := fun a =>
    sec_cancel u m (o'.etaA a) (o₂.etaA a) (by rw [hu]; exact (key a).2)
  refine ⟨g.left, ⟨hg, ⟨u, hη, hηA⟩, hu⟩, ?_⟩
  rintro h' ⟨hh', ⟨u', hu₁, hu₂⟩, hu'⟩
  have hu'' : u'.cm.F ≫ m.φ = m'.φ := hu'
  have hgg : (Over.homMk h' hh' : Over.mk f ⟶ V) = g := by
    apply hext
    · intro a
      ext1
      simp only [Over.comp_left, hχ a, Over.homMk_left]
      rw [← (key a).1, ← Category.assoc, ← hu₁ a, Category.assoc, hu'']
    · intro a
      ext1
      simp only [Over.comp_left, hθ a, Over.homMk_left]
      rw [← (key a).2, ← Category.assoc, ← hu₂ a, Category.assoc, hu'']
  rw [← hgg]
  rfl

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l l₂ : Level H}

theorem levelMap_over_field_noetherian (hL : Out.Laws)
    (Xo : Moduli D l) (Xo₂ : Moduli D l₂) (hpq : 1 ≤ D.p + D.q) (hd : l.Dvd l₂) (r : Xo₂.X ⟶ Xo.X)
    (m : SABMap Xo₂.univ.t Xo.univ.t r)
    (hm₁ : ∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left)
    (hm₂ : ∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left)
    (F : Type) [Field F] (b : Base l F) (b₂ : Base l₂ F) (j : KA l →+* F) (j₂ : KA l₂ →+* F)
    (e₁ : j (baseKA l).ρ = b.ρ) (e₂ : j (baseKA l).ζ = b.ζ) (e₃ : j₂ (baseKA l₂).ρ = b₂.ρ)
    (e₄ : j₂ (baseKA l₂).ζ = b₂.ζ) (hρ : b.ρ = b₂.ρ) (hζ : b.ζ = b₂.ζ ^ (l₂.A / l.A))
    (rF : pullback Xo₂.s (spMap j₂) ⟶ pullback Xo.s (spMap j))
    (h₁ : rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r) (h₂ : rF ≫ pullback.snd _ _ = pullback.snd _ _) :
    IsFinite rF ∧ Etale rF ∧ Surjective rF := by
  have hsm0 : Smooth Xo.s := by
    have := Xo.smooth
    exact SmoothOfRelativeDimension.smooth D.dim Xo.s
  have hsm0₂ : Smooth Xo₂.s := by
    have := Xo₂.smooth
    exact SmoothOfRelativeDimension.smooth D.dim Xo₂.s
  have hsmX : Smooth (pullback.snd Xo.s (spMap j)) := inferInstance
  have hsmX₂ : Smooth (pullback.snd Xo₂.s (spMap j₂)) := inferInstance
  obtain ⟨rX, -, nX⟩ := isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field F _ _ hsmX
  obtain ⟨rX₂, -, -⟩ := isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field F _ _ hsmX₂

  obtain ⟨o, ⟨no⟩⟩ := obj_pull E H D l (KA l) F (baseKA l) b j Xo.X (pullback Xo.s (spMap j)) Xo.s
    (pullback.snd _ _) (pullback.fst _ _) e₁ e₂ pullback.condition Xo.univ
  obtain ⟨o₂, ⟨no₂⟩⟩ := obj_pull E H D l₂ (KA l₂) F (baseKA l₂) b₂ j₂ Xo₂.X (pullback Xo₂.s (spMap j₂)) Xo₂.s
    (rF ≫ pullback.snd _ _) (pullback.fst _ _) e₃ e₄ (by rw [h₂]; exact pullback.condition) Xo₂.univ
  have hno1 : ∀ a, (o.eta a).left ≫ no.toSABMap.φ = pullback.fst _ _ ≫ (Xo.univ.eta a).left := no.2
  have hno2 : ∀ a, (o.etaA a).left ≫ no.toSABMap.φ = pullback.fst _ _ ≫ (Xo.univ.etaA a).left := no.3
  have hno₂1 : ∀ a, (o₂.eta a).left ≫ no₂.toSABMap.φ = pullback.fst _ _ ≫ (Xo₂.univ.eta a).left := no₂.2
  have hno₂2 : ∀ a, (o₂.etaA a).left ≫ no₂.toSABMap.φ = pullback.fst _ _ ≫ (Xo₂.univ.etaA a).left := no₂.3
  have hRX : Represents o := represents_pullback ObjMaps.id_comp_cancel Xo j
    (fun S s o' hS => moduli_rep_of_base ObjMaps.id_comp_cancel E H D l Xo F b j S s o' hS e₁ e₂) rfl o no
  have hRX₂ : Represents o₂ := represents_pullback ObjMaps.id_comp_cancel Xo₂ j₂
    (fun S s o' hS => moduli_rep_of_base ObjMaps.id_comp_cancel E H D l₂ Xo₂ F b₂ j₂ S s o' hS e₃ e₄) h₂ o₂ no₂

  obtain ⟨Y, π, oc, mc, hπf, hπe, hπs, hmc, huniv⟩ :=
    levelCover_noetherian hL E H D l l₂ F b b₂ _ (pullback.snd Xo.s (spMap j)) o nX hpq hd hρ hζ
  have hsmπ : Smooth π := inferInstance
  have hsmY : Smooth (π ≫ pullback.snd Xo.s (spMap j)) := inferInstance
  obtain ⟨rY, -, -⟩ := isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field F _ _ hsmY
  obtain ⟨o₁, ⟨n₁⟩⟩ := obj_pull E H D l F F b b (RingHom.id F) _ Y (pullback.snd _ _) (π ≫ pullback.snd _ _) π
    rfl rfl (by rw [spMap_id', Category.comp_id]) o

  obtain ⟨mcomp, hmcomp⟩ := sab_comp no₂.toSABMap m h₁.symm
  obtain ⟨m₂, hm₂'⟩ := sab_cancel no.toSABMap mcomp rF rfl
  have hm₂c : (∀ a, (o₂.eta a ^ (l₂.M / l.M)).left ≫ m₂.φ = rF ≫ (o.eta a).left) ∧
      (∀ a, (o₂.etaA a ^ (l₂.A / l.A)).left ≫ m₂.φ = rF ≫ (o.etaA a).left) := by
    constructor
    · intro a
      apply sec_cancel m₂ no.toSABMap
      rw [hm₂', hmcomp, ← Category.assoc, sec_pow _ _ _ (hno₂1 a), Category.assoc, hm₁ a, ← Category.assoc,
        ← h₁, Category.assoc, hno1 a]
    · intro a
      apply sec_cancel m₂ no.toSABMap
      rw [hm₂', hmcomp, ← Category.assoc, sec_pow _ _ _ (hno₂2 a), Category.assoc, hm₂ a, ← Category.assoc,
        ← h₁, Category.assoc, hno2 a]
  obtain ⟨h, hiso, hπ⟩ := iso_cover ObjMaps.id_comp_cancel (l₂.M / l.M) (l₂.A / l.A) o o₂ oc o₁ n₁ m₂ mc hm₂c hmc
    hRX hRX₂ rX₂ rY (obj_rigid_closed hL E H D l F F b b _ Y (pullback.snd _ _) (π ≫ pullback.snd _ _) o o₁ π
      (Or.inl rY)) huniv
  rw [← hπ]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end

theorem levelMap_finite_etale_surjective_of_laws (hL : Out.Laws) : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo : Moduli D l) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (r : Xo₂.X ⟶ Xo.X) (jK : KA l →+* KA l₂) (m : SABMap Xo₂.univ.t Xo.univ.t r), (∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) ∧ r ≫ Xo.s = Xo₂.s ≫ spMap jK ∧ (∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧ (∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left) → ∀ (c : Coeff l) (c₂ : Coeff l₂) (hc : c.F = c₂.F) (rF : Xo₂.XF c₂ ⟶ Xo.XF c), rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r → rF ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hc.le).toRingHom → IsFinite rF ∧ Etale rF ∧ Surjective rF := by
  intro E _ _ _ H D l l₂ Xo Xo₂ hpq hd r jK m hr c c₂ hc rF h₁ h₂
  obtain ⟨-, -, hm₁, hm₂⟩ := hr
  obtain ⟨F, fin, conj, zm, le⟩ := c
  obtain ⟨F₂, fin₂, conj₂, zm₂, le₂⟩ := c₂
  dsimp only at hc
  subst hc
  rw [spMap_inclusion_self, Category.comp_id] at h₂
  exact levelMap_over_field_noetherian hL Xo Xo₂ hpq hd r m hm₁ hm₂ F (baseOf l F le) (baseOf l₂ F le₂)
    (IntermediateField.inclusion le).toRingHom (IntermediateField.inclusion le₂).toRingHom rfl rfl rfl rfl
    (baseOf_rho l l₂ F le le₂) (baseOf_zeta l l₂ F le le₂ hd.2.2) rF h₁ h₂

end GlobalTheory.LevCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.MemNonzeroLocusOfIsActOf
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CoprimeTorsion

open CommutatorPairing

section General

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (T : Over S)

def chartPullLPow (n : ℕ) : ChartPull (LPow A L n T) (lbPow L n) (snd T A).left where
  idx j := fun _ => j 0
  le j y hy := mem_powChart.2 (Set.mem_iInter.1 hy 0)
  g y j j' hj hj' := by
    refine (gm_linComb L (fun _ : Fin 1 => (snd T A).left) (fun _ => (n : ℤ)) (𝟙 _) y j j' hj hj').trans
      (Eq.trans ?_ (gm_lbPow_g n (snd T A).left y _ _ (mem_powChart.2 (Set.mem_iInter.1 hj 0))
        (mem_powChart.2 (Set.mem_iInter.1 hj' 0))).symm)
    rw [Fin.prod_univ_one, Category.id_comp, zpow_natCast]

theorem nonzeroLocus_chartPullLPow (n : ℕ) (s : (lbPow L n).Sec) :
    nonzeroLocus (chartSec (chartPullLPow A L T n) s) = (snd T A).left ⁻¹ᵁ nonzeroLocus s :=
  nonzeroLocus_chartSec _ s fun _ J hJ => ⟨fun _ => J PUnit.unit, Set.mem_iInter.2 fun _ => mem_powChart.1 hJ⟩

def vanishing (a : ℤ) (E : Set (T ⊗ A).left) : Submodule Γ(T.left, ⊤) (SecM A L a T) where
  carrier := {f | ∀ y ∈ E, y ∉ nonzeroLocus (SecM.toSec A f)}
  add_mem' := by
    intro f f' hf hf' y hy h
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 h
    rcases Scheme.basicOpen_add_le _ (f.1 k) (f'.1 k) hk with h | h
    · exact hf y hy (Opens.mem_iSup.2 ⟨k, h⟩)
    · exact hf' y hy (Opens.mem_iSup.2 ⟨k, h⟩)
  zero_mem' := by
    intro y _ h
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 h
    exact (Scheme.basicOpen_zero _ _).le hk
  smul_mem' := by
    intro c f hf y hy h
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 h
    exact hf y hy (Opens.mem_iSup.2 ⟨k, ((Scheme.basicOpen_mul _ (liftHom A _ c) (f.1 k)).le hk).2⟩)

variable {A L T}

theorem mem_nonzeroLocus_of_isActOf (hL : L.IsLB) {a : ℤ} {θ : ThetaGrp A L a T} {s s' : LB.Sec (LPow A L a T)}
    (h : IsActOf A L a θ s s') {y : (T ⊗ A).left} (hy : y ∈ nonzeroLocus s') :
    (translT A θ.pt).left y ∈ nonzeroLocus s := by
  obtain ⟨k, hk, hu⟩ := (mem_nonzeroLocus s' y).1 hy
  obtain ⟨i, hi⟩ := exists_chart hL ((translPt A θ.pt).left y)
  obtain ⟨i₀, rfl⟩ : ∃ i₀ : L.ι, k = fun _ => i₀ := ⟨k 0, funext fun b => congrArg k (Subsingleton.elim _ _)⟩
  have hm : y ∈ LB.wchart L ![(snd T A).left, (translPt A θ.pt).left] ![i₀, i] := Set.mem_iInter.2 fun b => by
    fin_cases b
    exacts [Set.mem_iInter.1 hk 0, hi]
  have hp := chart_le_pull A L (translT A θ.pt) (translPt A θ.pt) (lift_snd _ _) ![i₀, i] hm
  have e := (gs_res (𝟙 _) y _ hm _).symm.trans ((congrArg (gs (𝟙 _) y _) (h ![i₀, i])).trans
    ((gs_mul (𝟙 _) y _ hm _ _).trans (congrArg (_ * ·) ((gs_res (𝟙 _) y _ hm _).trans
      (gs_pull (𝟙 _) (translT A θ.pt).left y _ hp _)))))
  have u := isUnit_of_mul_isUnit_right ((congrArg IsUnit e).mp hu)
  rw [Category.id_comp] at u
  exact (mem_nonzeroLocus_iff_pull s (translT A θ.pt).left y (k := fun _ => i) hp).2 u

end General

theorem dense_torsion (hA : AmpleSt) (hK : KerPowSt) (hI : IrredSt) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (P : PolAV (Sp k)) {p : ℕ} (hp : p.Prime) :
    Dense (⋃ x ∈ {x : 𝟙_ (Over (Sp k)) ⟶ P.A | ∃ n : ℕ, 0 < n ∧ n.Coprime p ∧ x ^ n = 1}, Set.range x.left) := by
  haveI : IsCommMonObj P.A := P.isAb.comm
  rw [dense_iff_inter_open]
  rintro U hU ⟨y₀, hy₀⟩
  by_contra hne
  obtain ⟨a, -, s, hs, hle, -⟩ := (isAmpleLB_of_relAmple_of_isAffine P.A P.isLB P.ample).exists_affine_le
    (U := ⟨U, hU⟩) hy₀
  have gen : ∀ N : ℕ, 4 ≤ N → ∀ y : P.A.left, ∃ t : (lbPow P.L N).Sec, y ∈ nonzeroLocus t := fun N hN y => by
    obtain ⟨m, t, ht, -⟩ := veryAmple_lbPow hA k P N hN
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (ht.ge (Set.mem_univ y))
    exact ⟨t i, hi⟩
  obtain ⟨m, hm, hmp⟩ : ∃ m : ℕ, 4 ≤ m ∧ m.Coprime p :=
    ⟨p * 2 + 1, by have := hp.two_le; omega, by simp⟩
  obtain ⟨t, ht⟩ := gen m hm y₀
  let n := a * p + m
  have hn : 4 ≤ n := le_add_left hm
  have hnp : n.Coprime p := by simpa [n] using hmp
  let σ : (lbPow P.L n).Sec := secMul (secPow s p) t
  have hσ : nonzeroLocus σ = nonzeroLocus s ⊓ nonzeroLocus t := by
    rw [nonzeroLocus_secMul, nonzeroLocus_secPow s hp.one_le]
  let B := baseOver (Sp k)
  let β : ∀ T : Over (Sp k), T ⟶ B := fun T => Over.homMk T.hom (Category.comp_id _)
  let E : Set (B ⊗ P.A).left := ⋃ x ∈ {x : 𝟙_ (Over (Sp k)) ⟶ P.A | ∃ n : ℕ, 0 < n ∧ n.Coprime p ∧ x ^ n = 1},
    Set.range (lift (β _) x).left
  have hsnd : ∀ {T : Over (Sp k)} (x : T ⟶ P.A) (z : T.left), (snd B P.A).left ((lift (β T) x).left z) = x.left z :=
    fun x z => congrArg (fun q => q.left z) (lift_snd (β _) x)
  rcases hI k P n (Or.inr hn) (Nat.cast_ne_zero.2 (by omega)) (vanishing P.A P.L B n E) (fun θ r r' hr h y hy hy' => by
      refine h _ ?_ (mem_nonzeroLocus_of_isActOf P.isLB hr hy')
      obtain ⟨x, ⟨l, hl, hlp, hx⟩, z, rfl⟩ := Set.mem_iUnion₂.1 hy
      have hθ : θ.pt ^ n = 1 := (hK _ P n (by omega) B θ.pt).1 fun q =>
        ⟨⊤, trivial, exists_isGen_pull _ θ.φ θ.isGen _⟩
      refine Set.mem_iUnion₂.2 ⟨(β _ ≫ θ.pt) * x, ⟨n * l, by positivity, Nat.Coprime.mul_left hnp hlp, ?_⟩, z,
        (congrArg (fun q => q.left z) (lift_translT θ.pt (β _) x)).symm⟩
      rw [mul_pow, pow_mul, pow_mul', hx, ← MonObj.comp_pow, hθ, MonObj.comp_one, one_pow, one_pow,
        _root_.mul_one]) with h | h
  · have hmem : SecM.ofSec P.A (chartSec (chartPullLPow P.A P.L B n) σ) ∈ vanishing P.A P.L B n E := fun y hy hy' => by
      obtain ⟨x, hx, z, rfl⟩ := Set.mem_iUnion₂.1 hy
      have h₁ : (snd B P.A).left ((lift (β _) x).left z) ∈ nonzeroLocus σ :=
        (nonzeroLocus_chartPullLPow P.A P.L B n σ).le hy'
      rw [hsnd, hσ] at h₁
      exact hne ⟨_, hle h₁.1, Set.mem_iUnion₂.2 ⟨x, hx, z, rfl⟩⟩
    rw [h, Submodule.mem_bot] at hmem
    have h₂ : (lift (β _) (𝟙 P.A)).left y₀ ∈ nonzeroLocus (chartSec (chartPullLPow P.A P.L B n) σ) :=
      (nonzeroLocus_chartPullLPow P.A P.L B n σ).ge (show (snd B P.A).left _ ∈ nonzeroLocus σ by
        rw [hsnd, hσ]; exact ⟨hs, ht⟩)
    exact (hmem ▸ (vanishing P.A P.L B n Set.univ).zero_mem :
      SecM.ofSec P.A (chartSec (chartPullLPow P.A P.L B n) σ) ∈ vanishing P.A P.L B n Set.univ) _ trivial h₂
  · let z : (𝟙_ (Over (Sp k))).left := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)
    obtain ⟨τ, hτ⟩ := gen n hn ((1 : 𝟙_ (Over (Sp k)) ⟶ P.A).left z)
    have hmem : SecM.ofSec P.A (chartSec (chartPullLPow P.A P.L B n) τ) ∈ vanishing P.A P.L B n E := by
      rw [h]; trivial
    refine hmem ((lift (β _) 1).left z) (Set.mem_iUnion₂.2 ⟨1, ⟨1, one_pos, by simp, one_pow _⟩, z, rfl⟩)
      ((nonzeroLocus_chartPullLPow P.A P.L B n τ).ge ?_)
    show (snd B P.A).left _ ∈ nonzeroLocus τ
    rw [hsnd]; exact hτ

end GlobalTheory.CoprimeTorsion
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionSectionCoordsThetaTimesRootsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_sectionCoords_theta_times_roots : Out.Laws → Out.Laws2 → ∀ (g m N' : ℕ), Odd N' → m ^ 2 ∣ N' → ∃ (e : Ix g (N' ^ 2) → Ix g (N' ^ 2) → ℕ) (idx : Ix g (N' ^ 2) → Ix g (N' ^ 2) → Ix g (N' ^ 2)), ∀ (o : Type) [CommRing o] (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (R : Type) [CommRing R] (β : o →+* R) (x : Sp R ⟶ S) (v : Ix g (N' ^ 2) → R) σ, x ≫ s = spMap β → t.HasTh x v → Ideal.span (Set.range v) = ⊤ → t.Emb m (Over.mk x) σ → ∀ h (y : Sp R ⟶ (Over.mk x ⊗ t.A).left), y = (lift (𝟙 (Over.mk x)) (((Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ t.lab h) ^ N')).left → ∀ p : Sp R, ∃ (R' : Type) (_ : CommRing R') (φ : R →+* R'), IsOpenImmersion (spMap φ) ∧ p ∈ Set.range (spMap φ) ∧ SecCoord _ σ (spMap φ ≫ y) (fun a => φ (β (b.ζ ^ e a h : oˣ) * v (idx a h))) := by
  first | exact @GlobalTheory.torsion_secCoord | exact GlobalTheory.torsion_secCoord | (intros; apply GlobalTheory.torsion_secCoord <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilPairingDiagonalBundleOfEighthPowerFormStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilPairing_diagonal_bundle_of_eighthPower_form : Out.GlobalFnsSt → ∀ (h k : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (S : Scheme.{0}) (G A : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A] (pr : Fin 8 → (G ⟶ A)) (L : LB G.left) (P : LB (G2 A).left) (K : Type) [Field K] (p : Sp K ⟶ S) (lev : (Fin h ⊕ Fin h → ℤ) → (Over.mk p ⟶ A)) (c : Γ((Over.mk p).left, ⊤)ˣ), IsE8 W → IsAbelianScheme G → IsAbelianScheme A → (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) → L.IsLB → P.IsLB → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → (∀ (T : Over S) (x x' y : T ⟶ A), (∃ t : (LB.LinComb P (K := Fin 3) ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]).Gen, t.IsGen) ∧ ∃ t : (LB.LinComb P (K := Fin 3) ![(lift y (x * x')).left, (lift y x).left, (lift y x').left] ![1, -1, -1]).Gen, t.IsGen) → LBIso L (LB.LinComb P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) → (∀ x y, lev (x + y) = lev x * lev y) → (∀ x, lev x ^ k = 1) → (∀ (X Y : Fin 8 → (Fin h ⊕ Fin h → ℤ)) (y y' : Over.mk p ⟶ G), (∀ u, y ≫ pr u = lev (X u)) → (∀ u, y' ≫ pr u = lev (Y u)) → Out.WeilIs G L k y y' (c ^ ∑ u, ∑ v, (W + W.transpose) u v * omegaStd (X u) (Y v))) → ∀ x y, Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (lev x) (lev y) (c ^ (2 * omegaStd x y)) := by
  first | exact @GlobalTheory.WeilDown.weilIs_diag | exact GlobalTheory.WeilDown.weilIs_diag | (intros; apply GlobalTheory.WeilDown.weilIs_diag <;> assumption)
end


import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.AdmissibleMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0283
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0291
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.CompatH
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle0004
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.RedGalBase
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionIsotropicSplitAllPlaces
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0289
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.Bundle0002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0254

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolynomialTransfer
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Site
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.PolyTfCon

variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

section Thickening

variable (T : Thick (nlFun γ 0 X q κ)) {l s : ℕ} (hT : TF l s T)

include hT in

theorem tr_facts : fil (trD T s) s = ⊥ ∧
    (∀ (r : ℕ) (x : trB T s), (l : trB T s) * x ∈ fil (trD T s) r → x ∈ fil (trD T s) r) ∧
    IsNilpotent (trJ T s) :=
  GlobalTheory.CompanionTheory.SiteTr.tr_tf T.δ l s (trD T s) (trD_spec T s).1 hT.1 hT.2

abbrev pT : Thick (nlFun γ 0 X q κ) :=
  polyTr T s ⟨fun h => absurd rfl h, fun _ => (tr_facts T hT).2.2⟩

abbrev jT : T ⟶ pT T hT := homOf _ _ _ _ _ _ _

theorem pT_tf : TF l s (pT T hT) := ⟨(tr_facts T hT).1, (tr_facts T hT).2.1⟩

abbrev xT : trB T s := Ideal.Quotient.mk (trI T s) ((pq T.B).e 1)

theorem e_mem (B : Type) [CommRing B] (J : Ideal B) : (pq B).e 1 ∈ (pq B).ext J :=
  Ideal.mem_sup_right (Ideal.subset_span ⟨0, rfl⟩)

theorem xT_mem : xT (s := s) T ∈ trJ T s := Ideal.mem_map_of_mem _ (e_mem _ _)

theorem sum_eq (b : ℕ →₀ T.B) :
    (b.sum fun k c => trF T s c * (trD T s).dpow k (xT (s := s) T)) =
      Ideal.Quotient.mk (trI T s) (b.sum fun k c => algebraMap T.B (pq T.B).P c * (eta T.δ).dpow k ((pq T.B).e 1)) := by
  rw [Finsupp.sum, Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, (trD_spec T s).1.dpow_comp _ (e_mem _ _)]
  rfl

theorem toNat_sub (r : ℤ) (k : ℕ) : (r - k).toNat = r.toNat - k := by omega

theorem fil_coeff (b : ℕ →₀ T.B) (r : ℤ) (hr : r ≤ s) :
    (b.sum fun k c => trF T s c * (trD T s).dpow k (xT (s := s) T)) ∈ fil (trD T s) r.toNat ↔
      ∀ k : ℕ, b k ∈ fil T.δ (r - k).toNat := by
  rw [sum_eq]
  simpa only [toNat_sub] using
    (GlobalTheory.CompanionTheory.SiteTrCrit.tr_crit T.δ s (trD T s) (trD_spec T s).1 b r.toNat (by omega) 0).1

theorem std_coeff (b : ℕ →₀ T.B) (r : ℤ) (hr : r ≤ s) (c : R) :
    (b.sum fun k c => trF T s c * (trD T s).dpow k (xT (s := s) T)) ∈
        fil (trD T s) r.toNat ⊔ Ideal.span {Ideal.Quotient.mk (trI T s) (algebraMap T.B (pq T.B).P (T.i c))} ↔
      ∀ k : ℕ, b k ∈ fil T.δ (r - k).toNat ⊔ Ideal.span {T.i c} := by
  rw [sum_eq]
  simpa only [toNat_sub] using
    (GlobalTheory.CompanionTheory.SiteTrCrit.tr_crit T.δ s (trD T s) (trD_spec T s).1 b r.toNat (by omega) (T.i c)).2

theorem univ_tr {T' : Thick (nlFun γ 0 X q κ)} (hT' : T'.pdPow s = ⊥) (φ : T ⟶ T') (x : T'.B) (hx : x ∈ T'.J) :
    ∃! ψ : pT T hT ⟶ T', jT T hT ≫ ψ = φ ∧ ψ.φ (xT (s := s) T) = x := by
  obtain ⟨F, ⟨hF1, hF2, hF3⟩, hFu⟩ := GlobalTheory.CompanionTheory.PDUniv.pdPoly_universal T.δ T'.δ φ.φ φ.dp x hx
  have hk : trI T s ≤ RingHom.ker F := by
    intro z hz
    have h1 : F z ∈ fil T'.δ (max s 1) := FubiniStudyChowHeightFormula₂.Adr.Fil.map_fil_le _ _ F hF3 _ (Ideal.mem_map_of_mem F hz)
    have h2 : fil T'.δ (max s 1) ≤ fil T'.δ s := GlobalTheory.Cris.ExpBij.dpFil_anti T'.δ (le_max_left _ _)
    have h3 : F z ∈ T'.pdPow s := h2 h1
    rw [hT'] at h3
    exact h3
  let g : trB T s →+* T'.B := Ideal.Quotient.lift (trI T s) F fun a ha => hk ha
  have hgF : g.comp (Ideal.Quotient.mk (trI T s)) = F := by
    refine RingHom.ext fun z => ?_
    exact Ideal.Quotient.lift_mk (trI T s) F fun a ha => hk ha
  have hg : g.comp (trF T s) = φ.φ := by
    rw [← RingHom.comp_assoc, hgF, hF1]
  have hdp : IsDPMorphism (trD T s) T'.δ g := (trD_spec T s).2 _ _ _ g (by rw [hgF]; exact hF3)
  have hle : trJ T s ≤ T'.J.comap g := Ideal.map_le_iff_le_comap.1 hdp.1
  refine ⟨descOf φ g hg hdp hle, ⟨hom_ext hg, (Ideal.Quotient.lift_mk (trI T s) F fun a ha => hk ha).trans hF2⟩, ?_⟩
  rintro ψ ⟨h1, h2⟩
  refine hom_ext ?_
  change ψ.φ = g
  have e := hFu (ψ.φ.comp (Ideal.Quotient.mk (trI T s))) ⟨?_, h2, ?_⟩
  · refine Ideal.Quotient.ringHom_ext ?_
    rw [e, hgF]
  · have := congrArg Thick.Hom.φ h1
    exact this
  · exact IsDPMorphism.comp _ ψ.dp (trD_spec T s).1

end Thickening

section Site

variable (l s : ℕ) (𝒱 : Set X.Opens)

abbrev Qc : ObjectProperty (Thick (nlFun γ 0 X q κ)) := St (TF l s) 𝒱

variable {l s 𝒱}

theorem pT_mem (T : (Qc (γ := γ) (q := q) (κ := κ) l s 𝒱).FullSubcategory) : Qc l s 𝒱 (pT T.obj T.property.1) := by
  obtain ⟨V, hV, h⟩ := T.property.2
  exact ⟨pT_tf _ _, V, hV, inU_hom (jT T.obj T.property.1) h⟩

variable (l s 𝒱)

def polyQ : Poly (sP (Qc (γ := γ) (q := q) (κ := κ) l s 𝒱)) where
  P T := ⟨pT T.obj T.property.1, pT_mem T⟩
  j T := ObjectProperty.homMk (jT T.obj T.property.1)
  X T := xT (s := s) T.obj
  X_mem T := xT_mem T.obj
  univ {T T'} φ x hx := by
    obtain ⟨ψ, ⟨h1, h2⟩, hu⟩ := univ_tr T.obj T.property.1 T'.property.1.1 φ.hom x hx
    refine ⟨ObjectProperty.homMk ψ, ⟨ObjectProperty.hom_ext _ h1, h2⟩, ?_⟩
    rintro ψ' ⟨h3, h4⟩
    exact ObjectProperty.hom_ext _ (hu ψ'.hom ⟨congrArg (fun f => f.hom) h3, h4⟩)
  span T z := by
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective (show trB T.obj s from z)
    obtain ⟨b, rfl⟩ := GlobalTheory.CompanionTheory.PDSpanning.exists_sum_dpow T.obj.δ w
    exact ⟨b, (sum_eq T.obj b).symm⟩

theorem crit_fil (r : ℤ) (hr : r ≤ s) : (polyQ (γ := γ) (q := q) (κ := κ) l s 𝒱).Crit (sFil _) r :=
  fun T b => fil_coeff T.obj b r hr

theorem crit_std (r : ℤ) (hr : r ≤ s) (c : R) :
    (polyQ (γ := γ) (q := q) (κ := κ) l s 𝒱).Crit (fun r => stdI _ (some r) c) r :=
  fun T b => std_coeff T.obj b r hr c

end Site

theorem polyTf : KH.PolyTf := by
  intro O R _ _ I γ X q κ l s 𝒱
  exact ⟨polyQ l s 𝒱, fun r hr => ⟨crit_fil l s 𝒱 r hr, crit_std l s 𝒱 r hr⟩⟩

end GlobalTheory.CompanionTheory.PolyTfCon
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullFrob
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.CrysPhi

theorem pull_frob {O : Type} [CommRing O] {F : Fn O} {b : Base} {ht : b.t = 1} {κ : O →+* b.R ⧸ b.I}
    {Λ : Type} [CommRing Λ] {c : Λ →+* b.R} {σ : b.R →+* b.R} {τ : Λ →+* Λ}
    (mo : GlobalTheory.LogCris.Mor (F.cr b ht κ) (F.cr b ht κ) σ) (h : ∀ a, σ (c a) = c (τ a))
    {C' : Type 1} [Category.{0} C'] {F' : C' ⥤ ModuleCat.{0} Λ}
    (Bm : CH.Mor (OM (F.cr b ht κ) c) F' (RingHom.id Λ)) (Ph : CH.Mor F' F' τ)
    (η : ∀ T, Bm.G.obj (Ph.G.obj T) ⟶ mo.obj (Bm.G.obj T))
    (nat : ∀ {T T' : C'} (f : T ⟶ T') (x : (Bm.G.obj (Ph.G.obj T)).B),
      (η T').φ ((Bm.G.map (Ph.G.map f)).φ x) = (Bm.G.map f).φ ((η T).φ x))
    (hτ : ∀ (T : C') (x : (Bm.G.obj (Ph.G.obj T)).B), Bm.τ T ((η T).φ x) = Ph.τ T (Bm.τ (Ph.G.obj T) x))
    (j : ℕ) (x : CH.H (OM (F.cr b ht κ) c) j) :
    Bm.pull j ((omMor mo τ h).pull j x) = Ph.pull j (Bm.pull j x) := by
  rw [pull_pull τ, pull_pull τ]
  exact (cr_pull_eq (Bm.comp Ph) ((omMor mo τ h).comp Bm) η nat hτ j x).symm

theorem qmap_frb {l : ℕ} [Fact l.Prime] {A : Type} [CommRing A] (J : Ideal A) (ph : A →+* A)
    (hl : (l : A ⧸ J) = 0) (hq : J ≤ J.comap ph)
    (hm : ∀ r, Ideal.Quotient.mk J (ph r) = Ideal.Quotient.mk J r ^ l) :
    Ideal.quotientMap J ph hq = frb hl :=
  Ideal.Quotient.ringHom_ext (RingHom.ext hm)

theorem pt_frb {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) {A : Type} [CommRing A] (J : Ideal A) (ph : A →+* A)
    (hl : (l : A ⧸ J) = 0) (hq : J ≤ J.comap ph)
    (hm : ∀ r, Ideal.Quotient.mk J (ph r) = Ideal.Quotient.mk J r ^ l) (z : F.Pt.obj (CommRingCat.of (A ⧸ J))) :
    F.Pt.map (CommRingCat.ofHom (Ideal.quotientMap J ph hq)) z = F.Pt.map (CommRingCat.ofHom (frb hl)) z := by
  rw [qmap_frb J ph hl hq hm]

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l)

def etaPhi (n : ℕ) (T : El (F.pt κ)) :
    (gT F κ true n).obj T ⟶ (SH.phiM F κ n).obj ((gT F κ true n).obj T) :=
  crHom (T := (gT F κ true n).obj T) (T' := (SH.phiM F κ n).obj ((gT F κ true n).obj T)) (((elπ (F.pt κ)).obj T).phi n)
    (fun r => (mapAcr_phi ((elπ (F.pt κ)).obj T).fromBase n r).symm) (((elπ (F.pt κ)).obj T).dpP_phi n) fun h => by
      exact pt_frb F (((elπ (F.pt κ)).obj T).PFil n) (((elπ (F.pt κ)).obj T).phi n)
        (l_zero ((gT F κ true n).obj T).y.1.1) h (phi_mk _ n) _

theorem phi_beta (n j : ℕ) (x : Hc F κ true n j) :
    β F κ true n j (phiHc F κ n j x) = (phiMor (F.pt κ) n).pull j (β F κ true n j x) :=
  pull_frob (SH.phiM F κ n) ((base l).phi_cris n) (βMor F κ true n) (phiMor (F.pt κ) n) (etaPhi F κ n)
    (fun f x => (mapAcr_phi ((elπ (F.pt κ)).map f) n x).symm) (fun _ _ => rfl) j x

end GlobalTheory.CompanionTheory.CrysPhi
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullInclRedMor
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.RedThick

theorem pull_incl_redMor : ∀ {O A R Λ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R] [CommRing Λ] {I : Ideal A} {γ : DividedPowers I}
    {J : Ideal R} {δ : DividedPowers J} {κ : O →+* R ⧸ J} {l n : ℕ} (d : RedIn δ κ γ l n) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (s s' : ℕ) (𝒱 : Set X.Opens) (h : TS γ q l s 𝒱 ≤ TS γ q l s' 𝒱) (c : Λ →+* R) (lam : Λ →+* A)
    (hc : ∀ a, d.ρ (c a) = Ideal.Quotient.mk _ (lam a)) (r : Option ℤ) (j : ℕ) (x : CH.H (B.OM (nlFun δ l X q κ) c) j),
    ((incl h).sq (a := IdF.top _) (a' := IdF.top _) (fun _ _ _ => trivial) (incl_std h r ((l : A) ^ n))).pull j
      ((redMor q s' d 𝒱 c lam hc r).pull j x) = (redMor q s d 𝒱 c lam hc r).pull j x := by
  intro O A R Λ _ _ _ _ _ I γ J δ κ l n d X q s s' 𝒱 h c lam hc r j x
  obtain ⟨⟨a, ha⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun u => ?_))
  change ((incl h).sq (a := IdF.top _) (a' := IdF.top _) (fun _ _ _ => trivial) (incl_std h r ((l : A) ^ n))).τ _
      ((redMor q s' d 𝒱 c lam hc r).τ _ (a (u ⋙ (ObjectProperty.ιOfLE h ⋙ redG q s' d 𝒱)))) =
    (redMor q s d 𝒱 c lam hc r).τ _ (a (u ⋙ redG q s d 𝒱))
  have key : ∀ z : (u.obj (Fin.last j)).obj.B ⧸ lnT (u.obj (Fin.last j)).obj l n,
      ((incl h).sq (a := IdF.top _) (a' := IdF.top _) (fun _ _ _ => trivial) (incl_std h r ((l : A) ^ n))).τ (u.obj (Fin.last j))
        ((redMor q s' d 𝒱 c lam hc r).τ ((ObjectProperty.ιOfLE h).obj (u.obj (Fin.last j))) z) =
      (redMor q s d 𝒱 c lam hc r).τ (u.obj (Fin.last j)) z := by
    intro z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    rfl
  exact key (a (u ⋙ redG q s d 𝒱))

end GlobalTheory.CompanionTheory.RedThick
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullRetype
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.RedNat

universe w w' v u v' u'

section Retype
variable {R R' : Type} [CommRing R] [CommRing R'] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R'} {σ σ₂ : R →+* R'}

def retype (m : CH.Mor F F' σ) (σ₂ : R →+* R') (h : ∀ T (a : R) (y : F'.obj T), σ a • y = σ₂ a • y) : CH.Mor F F' σ₂ where
  G := m.G
  τ T :=
    { toFun := m.τ T
      map_add' := map_add _
      map_smul' := fun a x => (LinearMap.map_smulₛₗ (m.τ T) a x).trans (h T a _) }
  nat := m.nat

theorem pull_retype (m : CH.Mor F F' σ) (h : ∀ T (a : R) (y : F'.obj T), σ a • y = σ₂ a • y) (n : ℕ) (x : CH.H F n) :
    (retype m σ₂ h).pull n x = m.pull n x := by
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj _ n).1 x
  have hb : CH.d F' n (m.pullC n a) = 0 := by rw [CH.Mor.d_pullC]; exact (congrArg _ ha).trans (map_zero _)
  exact (CrystallineSemistableComparison.P.mapH_cls (retype m σ₂ h).hom n a ha hb).trans (CrystallineSemistableComparison.P.mapH_cls m.hom n a ha hb).symm

end Retype

section Eta
variable {O A₁ A₂ R₁ R₂ : Type} [CommRing O] [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [CommRing R₁]
    [CommRing R₂] {I₁ : Ideal A₁} {I₂ : Ideal A₂} {γ₁ : DividedPowers I₁} {γ₂ : DividedPowers I₂}
    {J₁ : Ideal R₁} {J₂ : Ideal R₂} {δ₁ : DividedPowers J₁} {δ₂ : DividedPowers J₂} {κ₁ : O →+* R₁ ⧸ J₁} {κ₂ : O →+* R₂ ⧸ J₂}
    {l n s : ℕ} (d₁ : RedIn δ₁ κ₁ γ₁ l n) (d₂ : RedIn δ₂ κ₂ γ₂ l n) {X₁ X₂ : Scheme.{0}} {q₁ : X₁ ⟶ Spec (CommRingCat.of O)}
    {q₂ : X₂ ⟶ Spec (CommRingCat.of O)} {σ : A₁ →+* A₂} (nm : NMor γ₁ q₁ (κA O I₁) γ₂ q₂ (κA O I₂) σ) {σ' : R₁ →+* R₂}
    (m : Mor (nlFun δ₁ l X₁ q₁ κ₁) (nlFun δ₂ l X₂ q₂ κ₂) σ')

theorem eta_comm (hρ : ∀ x, d₂.ρ (σ' x) = lnMap σ l le_rfl (d₁.ρ x))
    (T : Thick (nlFun γ₂ 0 X₂ q₂ (κA O I₂))) (r : R₁) :
    iBar ((nm.mor 0).obj T) l n (d₁.ρ r) = iBar T l n (d₂.ρ (σ' r)) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (d₁.ρ r)
  rw [hρ, ← ha]
  rfl

def etaR (hpt : ∀ (B : CommRingCat.{0}) (y : PtOver X₂ q₂ κ₂ B), (show PtOver X₁ q₁ κ₁ B from m.pt.app B y).1.2 = y.1.2 ≫ nm.u)
    (hρ : ∀ x, d₂.ρ (σ' x) = lnMap σ l le_rfl (d₁.ρ x))
    (T : Thick (nlFun γ₂ 0 X₂ q₂ (κA O I₂))) (h₁ : TF l s ((nm.mor 0).obj T)) (h₂ : TF l s T) :
    redObj ((nm.mor 0).obj T) d₁ h₁ ⟶ m.obj (redObj T d₂ h₂) :=
  mkH (show T.B ⧸ lnT T l n →+* T.B ⧸ lnT T l n from RingHom.id _) (fun r => eta_comm d₁ d₂ nm hρ T r)
    ⟨le_of_eq (Ideal.map_id _), fun x hx => rfl⟩ (fun x hx => hx) (by
      refine Subtype.ext (Prod.ext ?_ ?_)
      · refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_)
        have hw1 := (redObj ((nm.mor 0).obj T) d₁ h₁).w r
        have hw2 := (m.obj (redObj T d₂ h₂)).w r
        have h3 : Ideal.Quotient.mk (m.obj (redObj T d₂ h₂)).J ((redObj ((nm.mor 0).obj T) d₁ h₁).i r) =
            Ideal.Quotient.mk (m.obj (redObj T d₂ h₂)).J ((m.obj (redObj T d₂ h₂)).i r) :=
          congrArg (Ideal.Quotient.mk (m.obj (redObj T d₂ h₂)).J) (eta_comm d₁ d₂ nm hρ T r)
        exact (congrArg (Ideal.quotientMap (m.obj (redObj T d₂ h₂)).J
          (show T.B ⧸ lnT T l n →+* T.B ⧸ lnT T l n from RingHom.id _) (fun x hx => hx)) hw1).trans (h3.trans hw2.symm)
      · have e := hpt _ (redObj T d₂ h₂).y
        refine Eq.trans ?_ e.symm
        change Spec.map _ ≫ Spec.map (CommRingCat.ofHom (qBar ((nm.mor 0).obj T) l n)) ≫ (pt T ≫ nm.u) =
          (Spec.map (CommRingCat.ofHom (qBar T l n)) ≫ pt T) ≫ nm.u
        rw [Category.assoc, ← Category.assoc, ← Spec.map_comp]
        congr 2
        exact CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)))

end Eta

section Main
variable {O A₁ A₂ R₁ R₂ Λ₁ Λ₂ : Type} [CommRing O] [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [CommRing R₁]
    [CommRing R₂] [CommRing Λ₁] [CommRing Λ₂] {I₁ : Ideal A₁} {I₂ : Ideal A₂} {γ₁ : DividedPowers I₁} {γ₂ : DividedPowers I₂}
    {J₁ : Ideal R₁} {J₂ : Ideal R₂} {δ₁ : DividedPowers J₁} {δ₂ : DividedPowers J₂} {κ₁ : O →+* R₁ ⧸ J₁} {κ₂ : O →+* R₂ ⧸ J₂}
    {l n : ℕ} (d₁ : RedIn δ₁ κ₁ γ₁ l n) (d₂ : RedIn δ₂ κ₂ γ₂ l n) {X₁ X₂ : Scheme.{0}} {q₁ : X₁ ⟶ Spec (CommRingCat.of O)}
    {q₂ : X₂ ⟶ Spec (CommRingCat.of O)} (s : ℕ) {σ : A₁ →+* A₂} (nm : NMor γ₁ q₁ (κA O I₁) γ₂ q₂ (κA O I₂) σ) {σ' : R₁ →+* R₂}
    (m : Mor (nlFun δ₁ l X₁ q₁ κ₁) (nlFun δ₂ l X₂ q₂ κ₂) σ') (c₁ : Λ₁ →+* R₁) (c₂ : Λ₂ →+* R₂) (lam₁ : Λ₁ →+* A₁) (lam₂ : Λ₂ →+* A₂)
    (hc₁ : ∀ a, d₁.ρ (c₁ a) = Ideal.Quotient.mk _ (lam₁ a)) (hc₂ : ∀ a, d₂.ρ (c₂ a) = Ideal.Quotient.mk _ (lam₂ a))
    (σ₀ : Λ₁ →+* Λ₂) (h₀ : ∀ a, σ' (c₁ a) = c₂ (σ₀ a))

include hc₁ hc₂ h₀ in

theorem lam_mem (hρ : ∀ x, d₂.ρ (σ' x) = lnMap σ l le_rfl (d₁.ρ x)) (a : Λ₁) :
    σ (lam₁ a) - lam₂ (σ₀ a) ∈ Ideal.span {(l : A₂) ^ n} := by
  refine Ideal.Quotient.eq.1 ?_
  have e := hρ (c₁ a)
  rw [h₀, hc₂, hc₁] at e
  exact e.symm

include hc₁ hc₂ h₀ in

theorem lam_smul (hρ : ∀ x, d₂.ρ (σ' x) = lnMap σ l le_rfl (d₁.ρ x)) (r : Option ℤ)
    (T : (TS γ₂ q₂ l s {⊤}).FullSubcategory) (a : Λ₁)
    (y : (sq (IdF.top (sP (TS γ₂ q₂ l s {⊤})).A) (stdI (TS γ₂ q₂ l s {⊤}) r ((l : A₂) ^ n))).obj T) :
    (σ.comp lam₁) a • y = (lam₂.comp σ₀) a • y := by
  obtain ⟨y, hy⟩ := y
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine Subtype.ext (Ideal.Quotient.eq.2 ?_)
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 (lam_mem d₁ d₂ c₁ c₂ lam₁ lam₂ hc₁ hc₂ σ₀ h₀ hρ a)
  refine ln_le q₂ s {⊤} r T ?_
  change T.obj.i (σ (lam₁ a)) * (show T.obj.B from b) - T.obj.i (lam₂ (σ₀ a)) * (show T.obj.B from b) ∈ lnT T.obj l n
  rw [← sub_mul, ← map_sub, ← hz, map_mul, map_pow, map_natCast]
  exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))

end Main

theorem red_nm : ∀ {O A₁ A₂ R₁ R₂ Λ₁ Λ₂ : Type} [CommRing O] [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [CommRing R₁]
    [CommRing R₂] [CommRing Λ₁] [CommRing Λ₂] {I₁ : Ideal A₁} {I₂ : Ideal A₂} {γ₁ : DividedPowers I₁} {γ₂ : DividedPowers I₂}
    {J₁ : Ideal R₁} {J₂ : Ideal R₂} {δ₁ : DividedPowers J₁} {δ₂ : DividedPowers J₂} {κ₁ : O →+* R₁ ⧸ J₁} {κ₂ : O →+* R₂ ⧸ J₂}
    {l n : ℕ} (d₁ : RedIn δ₁ κ₁ γ₁ l n) (d₂ : RedIn δ₂ κ₂ γ₂ l n) {X₁ X₂ : Scheme.{0}} {q₁ : X₁ ⟶ Spec (CommRingCat.of O)}
    {q₂ : X₂ ⟶ Spec (CommRingCat.of O)} (s : ℕ) {σ : A₁ →+* A₂} (nm : NMor γ₁ q₁ (κA O I₁) γ₂ q₂ (κA O I₂) σ) {σ' : R₁ →+* R₂}
    (m : Mor (nlFun δ₁ l X₁ q₁ κ₁) (nlFun δ₂ l X₂ q₂ κ₂) σ') (c₁ : Λ₁ →+* R₁) (c₂ : Λ₂ →+* R₂) (lam₁ : Λ₁ →+* A₁) (lam₂ : Λ₂ →+* A₂)
    (hc₁ : ∀ a, d₁.ρ (c₁ a) = Ideal.Quotient.mk _ (lam₁ a)) (hc₂ : ∀ a, d₂.ρ (c₂ a) = Ideal.Quotient.mk _ (lam₂ a))
    (σ₀ : Λ₁ →+* Λ₂) (h₀ : ∀ a, σ' (c₁ a) = c₂ (σ₀ a)),
    (∀ (B : CommRingCat.{0}) (y : PtOver X₂ q₂ κ₂ B), (show PtOver X₁ q₁ κ₁ B from m.pt.app B y).1.2 = y.1.2 ≫ nm.u) →
    (∀ x, d₂.ρ (σ' x) = lnMap σ l le_rfl (d₁.ρ x)) → ∀ (r : Option ℤ) (j : ℕ) (x : CH.H (B.OM (nlFun δ₁ l X₁ q₁ κ₁) c₁) j),
    (redMor q₂ s d₂ {⊤} c₂ lam₂ hc₂ r).pull j ((B.omMor m σ₀ h₀).pull j x) =
      nmHM nm l s r n j ((redMor q₁ s d₁ {⊤} c₁ lam₁ hc₁ r).pull j x) := by
  intro O A₁ A₂ R₁ R₂ Λ₁ Λ₂ _ _ _ _ _ _ _ _ _ I₁ I₂ γ₁ γ₂ J₁ J₂ δ₁ δ₂ κ₁ κ₂ l n d₁ d₂ X₁ X₂ q₁ q₂ s σ nm σ' m c₁ c₂ lam₁ lam₂
    hc₁ hc₂ σ₀ h₀ hpt hρ r j x
  let S2 := (nmS nm l s).sq (a := IdF.top _) (a' := IdF.top _) (fun _ _ _ => trivial) (nm_std nm l s r n)
  letI t1 : RingHomCompTriple σ₀ lam₂ (lam₂.comp σ₀) := ⟨rfl⟩
  letI t2 : RingHomCompTriple lam₁ σ (σ.comp lam₁) := ⟨rfl⟩
  let M1 : CH.Mor _ _ (lam₂.comp σ₀) := (B.omMor m σ₀ h₀).comp (redMor q₂ s d₂ {⊤} c₂ lam₂ hc₂ r)
  let M2 : CH.Mor _ _ (σ.comp lam₁) := (redMor q₁ s d₁ {⊤} c₁ lam₁ hc₁ r).comp S2
  have hsc := lam_smul (q₂ := q₂) d₁ d₂ s c₁ c₂ lam₁ lam₂ hc₁ hc₂ σ₀ h₀ hρ r
  have h1 := (CrystallineSemistableComparison.P.pull_comp (σ'' := lam₂.comp σ₀) (B.omMor m σ₀ h₀) (redMor q₂ s d₂ {⊤} c₂ lam₂ hc₂ r) j x).1
  have h2 := (CrystallineSemistableComparison.P.pull_comp (σ'' := σ.comp lam₁) (redMor q₁ s d₁ {⊤} c₁ lam₁ hc₁ r) S2 j x).1
  have h3 := pull_retype M2 (σ₂ := lam₂.comp σ₀) hsc j x
  let η : (retype M2 (lam₂.comp σ₀) hsc).G ⟶ M1.G :=
    { app := fun T => etaR d₁ d₂ nm m hpt hρ T.obj T.property.1 T.property.1
      naturality := fun T T' f => hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)) }
  have h4 := CrystallineSemistableComparison.P.prism (retype M2 (lam₂.comp σ₀) hsc) M1 η (fun T y => by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective (I := lnT T.obj l n) y
    rfl) j x
  exact h1.symm.trans (h4.symm.trans (h3.trans h2))

end GlobalTheory.CompanionTheory.RedNat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullUnitClass
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.SiteCup

theorem pull_unit_class {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
    {σ : R →+* R'} (A : C ⥤ CommAlgCat.{0} R) (A' : C' ⥤ CommAlgCat.{0} R')
    (m : CH.Mor (CH.modF A) (CH.modF A') σ)
    (h : ∀ T : C', m.τ T (1 : A.obj (m.G.obj T)) = (1 : A'.obj T)) :
    m.pull 0 (CH.oneH A) = CH.oneH A' := by
  unfold CH.Mor.pull CH.oneH
  generalize_proofs p1 p2
  rw [CrystallineSemistableComparison.P.mapH_cls]
  · congr 1
    funext s
    exact h _
  · convert p2 using 2
    funext s
    exact h _

theorem smor_cup : ∀ {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {Φ : PDF R C}
    {Φ' : PDF R' C'} {σ : R →+* R'} (m : SMor Φ Φ' σ), (∀ {i j k : ℕ} (h : i + j = k) x y,
      m.o.pull k ((CH.mulP Φ.A).cup h x y) = (CH.mulP Φ'.A).cup h (m.o.pull i x) (m.o.pull j y)) ∧
    m.o.pull 0 (CH.oneH Φ.A) = CH.oneH Φ'.A := by
  intro R R' _ _ C C' _ _ Φ Φ' σ m
  refine ⟨?_, pull_unit_class _ _ m.o (fun T => RingHom.map_one (m.ρ T))⟩
  intro i j k h x y
  have hz : ∀ n (c : (CH.cx (CH.modF Φ.A)).X n), c ∈ (CH.cx (CH.modF Φ.A)).Z n →
      m.o.hom.f n c ∈ (CH.cx (CH.modF Φ'.A)).Z n := by
    intro n c hc
    refine LinearMap.mem_ker.mpr ?_
    rw [m.o.hom.comm, LinearMap.mem_ker.mp hc, map_zero]
  have ex := CrystallineSemistableComparison.Auxff.cls_out _ x
  generalize Quotient.out x = z at ex
  subst ex
  have ey := CrystallineSemistableComparison.Auxff.cls_out _ y
  generalize Quotient.out y = w at ey
  subst ey
  obtain ⟨a, ha⟩ := z
  obtain ⟨b, hb⟩ := w
  obtain ⟨hc, e⟩ := CrystallineSemistableComparison.P.cup_cls (CH.mulP Φ.A) h a b ha hb
  obtain ⟨hc', e'⟩ := CrystallineSemistableComparison.P.cup_cls (CH.mulP Φ'.A) h _ _ (hz _ _ ha) (hz _ _ hb)
  rw [e]
  unfold CH.Mor.pull
  rw [CrystallineSemistableComparison.P.mapH_cls _ _ _ _ (hz _ _ ha), CrystallineSemistableComparison.P.mapH_cls _ _ _ _ (hz _ _ hb), e',
    CrystallineSemistableComparison.P.mapH_cls _ _ _ _ (hz _ _ hc)]
  congr 1
  funext s
  simp [CH.Mor.hom, CH.Mor.pullC, CH.mulP, CH.Pairing.cupC, SMor.o, CH.term, CH.modF]
  congr 1 <;> exact m.nat _ _

end GlobalTheory.CompanionTheory.SiteCup
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionIsotropicSplitAllPlacesStatement
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quaternion_isotropic_split_all_places : ∀ {F : Type} [Field F] [NumberField F] (d β : F), (∀ r : F, r ^ 2 ≠ d) → β ≠ 0 →
  (∃ x : Q d β F, x ≠ 0 ∧ qn x = 0) → ∀ s : Pl F, QSA d β s := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.Split.strong_approx_split | exact GlobalTheory.CompanionTheory.PlaneSA.Split.strong_approx_split | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.Split.strong_approx_split <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuotientMapFactor
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.BetaCmp

theorem quotientMap_factor {B : Type} [CommRing B] {I J K : Ideal B} (hJ : I ≤ J) (hK : I ≤ K) (h : J ≤ K.comap (RingHom.id B))
    (w : B ⧸ I) : Ideal.quotientMap K (RingHom.id B) h (Ideal.Quotient.factor hJ w) = Ideal.Quotient.factor hK w := by
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective w
  rfl

theorem pt_uJ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (A : PAlg l) (n : ℕ) (y : F.Pt.obj (CommRingCat.of A.U))
    (h : JJ false A n ≤ (JJ true A n).comap (RingHom.id _)) :
    F.Pt.map (CommRingCat.ofHom (Ideal.quotientMap (JJ true A n) (RingHom.id _) h)) (F.Pt.map (CommRingCat.ofHom (uJ false A n)) y) =
      F.Pt.map (CommRingCat.ofHom (uJ true A n)) y := by
  have e : (Ideal.quotientMap (JJ true A n) (RingHom.id _) h).comp (uJ false A n) = uJ true A n :=
    RingHom.ext fun x => quotientMap_factor (fil_le false A n) (fil_le true A n) h _
  rw [← Functor.map_comp_apply, ← CommRingCat.ofHom_comp, e]

theorem β_cmp : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (n j : ℕ) (x : Hc F κ false n j), β F κ true n j ((cmpMor F κ n).pull j x) = β F κ false n j x := by
  intro l _ O _ F κ n j x
  have e : β F κ true n j ((cmpMor F κ n).pull j x) =
      ((cmpMor F κ n).comp (σ'' := RingHom.id _) (βMor F κ true n)).pull j x :=
    pull_pull (RingHom.id _) (cmpMor F κ n) (βMor F κ true n) j x
  refine e.trans ?_
  refine (cr_pull_eq (βMor F κ false n) ((cmpMor F κ n).comp (σ'' := RingHom.id _) (βMor F κ true n))
    (fun T => crHom (RingHom.id _) (fun _ => rfl) (T.1.obj.dp_fil_pfil n) ?_) ?_ ?_ j x).symm
  · intro h
    exact pt_uJ F T.1.obj n T.2.1 h
  · intro T T' f z; rfl
  · intro T z; rfl

end GlobalTheory.CompanionTheory.BetaCmp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedKillsToSome
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.RedFil

theorem red_kills_toSome : ∀ {O A R Λ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R] [CommRing Λ] {I : Ideal A} {γ : DividedPowers I}
    {J : Ideal R} {δ : DividedPowers J} {κ : O →+* R ⧸ J} {l n : ℕ} (d : RedIn δ κ γ l n) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (s : ℕ) (𝒱 : Set X.Opens) (c : Λ →+* R) (lam : Λ →+* A)
    (hc : ∀ a, d.ρ (c a) = Ideal.Quotient.mk _ (lam a)) (r j : ℕ), ∀ x ∈ (B.pdS (nlFun δ l X q κ) c r).img j,
    toSome (TS γ q l s 𝒱) r ((l : A) ^ n) j ((redMor q s d 𝒱 c lam hc none).pull j x) = 0 := by
  intro O A R Λ _ _ _ _ _ I γ J δ κ l n d X q s 𝒱 c lam hc r j x hx
  exact GlobalTheory.CompanionTheory.RedFil.red_kills d q s 𝒱 c lam hc r j x hx

end GlobalTheory.CompanionTheory.RedFil
end


import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0568
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0023
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0025
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0037
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentVecC
import Formalism.LocalToGlobal.ProjectiveLattices.FrCovA
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.SubsingletonRankIndicatorIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0570
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0115
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0572
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegerExponentSectionOfChartRegular
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.SecGlueInt

open GlobalTheory.Reg.ChartCompat (comp_eq away_lift away_inj)
open GlobalTheory.Reg.SecGlue (chart_comp eq_of_fields)

def zchar {J S : Type} [Fintype J] [CommRing S] (e : J → ℤ) (t : J → Sˣ) : S := ((∏ i, t i ^ e i : Sˣ) : S)

theorem zchar_mul {J S : Type} [Fintype J] [CommRing S] (e : J → ℤ) (t t' : J → Sˣ) :
    zchar e (t * t') = zchar e t * zchar e t' := by
  simp only [zchar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib, Units.val_mul]

theorem zchar_one {J S : Type} [Fintype J] [CommRing S] (e : J → ℤ) : zchar e (1 : J → Sˣ) = 1 := by
  simp [zchar]

theorem zchar_map {J K S T : Type} [Fintype J] [Field K] [CommRing S] [CommRing T] [Algebra K S] [Algebra K T]
    (φ : S →ₐ[K] T) (e : J → ℤ) (t : J → Sˣ) :
    zchar e (fun i => Units.map (φ : S →* T) (t i)) = φ (zchar e t) := by
  have : (∏ i, Units.map (φ : S →* T) (t i) ^ e i) = Units.map (φ : S →* T) (∏ i, t i ^ e i) := by
    simp only [map_prod, map_zpow]
  unfold zchar
  rw [this]
  rfl

set_option maxHeartbeats 1000000 in

theorem chart_compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ h : GenFrEx Xo c, ∀ (C C' : FChart h) (L : Type) [Field L] [Algebra c.F L] (ψ : C.R →ₐ[c.F] L) (ψ' : C'.R →ₐ[c.F] L) (z z' : FrPt Xo c L) (t : Ix Dw → Lˣ), FrMap ψ C.y z → FrMap ψ' C'.y z' → FrBor t z z' → C.Z = C'.Z ∧ ∀ (e : Ix Dw → ℤ) (b : ∀ Z : Comp Xo c, Om Z) (hb : zchar e C.t * b C.Z ∈ C.R) (hb' : zchar e C'.t * b C'.Z ∈ C'.R), ψ' ⟨_, hb'⟩ = zchar e t * ψ ⟨_, hb⟩ := by
  intro E _ _ _ H Dw l Xo c hev h C C' L _ _ ψ ψ' z z' t hz hz' hbor
  have G := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c
  have U := GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c
  obtain ⟨g, hg, hopn⟩ := C'.opn C.R L ψ C.y z hz ⟨ψ', z', t⁻¹, hz', (G L).2.2.1 t z z' hbor⟩
  have hg0 : g ≠ 0 := fun e => hg (by rw [e, map_zero])
  have hg1 : C.R.val g ≠ 0 := fun e => hg0 (Subtype.ext e)
  have hZ : C.Z = C'.Z := by
    obtain ⟨ψ0, z0, t0, h1, h2⟩ := hopn (Om C.Z) C.R.val (Ne.isUnit hg1) C.yg C.gen
    exact comp_eq C C' ψ0 z0 t0 h1 h2
  refine ⟨hZ, ?_⟩
  obtain ⟨Z, R, sm, frac, y, yg, tC, gen, bor, mono, opn⟩ := C
  obtain ⟨Z', R', sm', frac', y', yg', tC', gen', bor', mono', opn'⟩ := C'
  dsimp only at *
  subst hZ
  intro e b hb hb'
  let S := Localization.Away g
  let lam : R →ₐ[c.F] S := IsScalarTower.toAlgHom c.F R S
  have hlam : IsUnit (lam g) := IsLocalization.Away.algebraMap_isUnit g
  obtain ⟨mu, hmu⟩ : ∃ m : S →ₐ[c.F] Om Z, m.comp lam = R.val := away_lift g R.val hg1
  obtain ⟨nu, hnu⟩ : ∃ m : S →ₐ[c.F] L, m.comp lam = ψ := away_lift g ψ hg
  have hinj : Function.Injective mu := away_inj g mu (by rw [hmu]; exact Subtype.val_injective)
  obtain ⟨w, hw⟩ := hev.bc R S lam y
  obtain ⟨φ, v, s, hv, hs⟩ := hopn S lam hlam w hw

  obtain ⟨vmu, hvmu⟩ := hev.bc S (Om Z) mu v
  have m1 : FrMap mu w yg := frMap_cancel _ _ _ lam mu y w yg hw (by rw [hmu]; exact gen)
  have b1 := frBorBC _ _ mu s v w vmu yg hs hvmu m1
  have m2 : FrMap (mu.comp φ) y' vmu := frMap_trans _ _ _ φ mu y' v vmu hv hvmu
  have b2 := (G _).2.1 _ _ _ _ _ b1 ((G _).2.1 _ _ _ _ _ ((G _).2.2.1 _ _ _ bor) bor')
  have e1 : mu.comp φ = R'.val := mono' _ _ _ _ _ _ m2 gen' b2
  have e2 : vmu = yg' := (U _ _ R'.val y').1 _ _ (e1 ▸ m2) gen'
  subst e2
  have e3 : tC = tC' * fun i => Units.map (mu : S →* Om Z) (s i) :=
    (G _).2.2.2 _ _ _ _ bor ((G _).2.1 _ _ _ _ _ bor' b1)

  obtain ⟨vnu, hvnu⟩ := hev.bc S L nu v
  have m3 : FrMap nu w z := frMap_cancel _ _ _ lam nu y w z hw (by rw [hnu]; exact hz)
  have b3 := frBorBC _ _ nu s v w vnu z hs hvnu m3
  have m4 : FrMap (nu.comp φ) y' vnu := frMap_trans _ _ _ φ nu y' v vnu hv hvnu
  have b4 := (G _).2.1 _ _ _ _ _ b3 hbor
  have e4 : nu.comp φ = ψ' := mono' _ _ _ _ _ _ m4 hz' b4
  have e5 : vnu = z' := (U _ _ ψ' y').1 _ _ (e4 ▸ m4) hz'
  subst e5
  have e6 : (fun i => Units.map (nu : S →* L) (s i)) * t = 1 :=
    (G _).2.2.2 _ _ _ _ b4 ((G _).1 _)
  have e7 : lam ⟨_, hb⟩ = zchar e s * φ ⟨_, hb'⟩ := by
    apply hinj
    have a1 : mu (lam ⟨_, hb⟩) = zchar e tC * b Z := DFunLike.congr_fun hmu ⟨_, hb⟩
    have a2 : mu (φ ⟨_, hb'⟩) = zchar e tC' * b Z := DFunLike.congr_fun e1 ⟨_, hb'⟩
    have a0 : zchar e tC = zchar e tC' * mu (zchar e s) :=
      (congrArg (zchar e) e3).trans ((zchar_mul _ _ _).trans (congrArg _ (zchar_map mu e s)))
    rw [map_mul, a1, a2]
    linear_combination (b Z) * a0
  have a3 : ψ ⟨_, hb⟩ = nu (zchar e s) * ψ' ⟨_, hb'⟩ := by
    rw [← hnu, ← e4, AlgHom.comp_apply, AlgHom.comp_apply, e7, map_mul]
  have a4 : nu (zchar e s) * zchar e t = 1 := by
    rw [← zchar_map, ← zchar_mul, e6, zchar_one]
  linear_combination (-(zchar e t)) * a3 - (ψ' ⟨_, hb'⟩) * a4

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

section Val

variable {h : GenFrEx Xo c} {e : Ix Dw → ℤ} {b : ∀ Z : Comp Xo c, Om Z}
  (hb : ∀ C : FChart h, zchar e C.t * b C.Z ∈ C.R)

def Val {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S) : Prop :=
  ∃ (C : FChart h) (ψ : C.R →ₐ[c.F] S) (z : FrPt Xo c S) (t : Ix Dw → Sˣ),
    FrMap ψ C.y z ∧ FrBor t z y ∧ v = zchar e t * ψ ⟨_, hb C⟩

theorem val_unique (hl : EvLaws Xo c) {L : Type} [Field L] [Algebra c.F L] {y : FrPt Xo c L} {v v' : L}
    (h1 : Val hb y v) (h2 : Val hb y v') : v = v' := by
  obtain ⟨C, ψ, z, t, hz, ht, rfl⟩ := h1
  obtain ⟨C', ψ', z', t', hz', ht', rfl⟩ := h2
  obtain ⟨-, hmul, hinv, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c L
  have := (chart_compat E H Dw l Xo c hl h C C' L ψ ψ' z z' _ hz hz'
    (hmul _ _ _ _ _ ht (hinv _ _ _ ht'))).2 e b (hb C) (hb C')
  rw [this, ← mul_assoc, ← zchar_mul, mul_comm t, mul_inv_cancel_left]

theorem val_map (hl : EvLaws Xo c) {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) {y : FrPt Xo c S} {y' : FrPt Xo c T} (hy : FrMap φ y y') {v : S} (h1 : Val hb y v) :
    Val hb y' (φ v) := by
  obtain ⟨C, ψ, z, t, hz, ht, rfl⟩ := h1
  obtain ⟨z', hz'⟩ := hl.bc S T φ z
  refine ⟨C, φ.comp ψ, z', _, frMap_trans _ _ _ ψ φ _ _ _ hz hz', frBorBC _ _ φ t z y z' y' ht hz' hy, ?_⟩
  rw [zchar_map, map_mul]; rfl

theorem val_bor {S : Type} [CommRing S] [Algebra c.F S] {t : Ix Dw → Sˣ} {y y' : FrPt Xo c S}
    (hy : FrBor t y y') {v : S} (h1 : Val hb y v) : Val hb y' (zchar e t * v) := by
  obtain ⟨C, ψ, z, t₀, hz, ht, rfl⟩ := h1
  refine ⟨C, ψ, z, t₀ * t, hz, (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c S).2.1 _ _ _ _ _ ht hy, ?_⟩
  rw [zchar_mul]; ring

theorem val_ex (hA : Atlas h) {L : Type} [Field L] [Algebra c.F L] (y : FrPt Xo c L) : ∃ v, Val hb y v := by
  obtain ⟨C, ψ, z, t, h1, h2⟩ := hA L y
  exact ⟨_, C, ψ, z, t, h1, h2, rfl⟩

theorem val_gen (hA : Atlas h) (Z : Comp Xo c) : Val hb (genFr h Z) (b Z) := by
  obtain ⟨C, ψ, z, t, h1, h2⟩ := hA _ (genFr h Z)
  obtain rfl := chart_comp Z C ψ z t h1 h2
  refine ⟨C, C.R.val, C.yg, C.t⁻¹, C.gen, (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c _).2.2.1 _ _ _ C.bor, ?_⟩
  show b C.Z = zchar e C.t⁻¹ * (zchar e C.t * b C.Z)
  rw [← mul_assoc, ← zchar_mul, inv_mul_cancel, zchar_one, one_mul]

def Rep {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (g s : S) : Prop :=
  ∀ (L : Type) [Field L] [Algebra c.F L] (χ : S →ₐ[c.F] L) (w : FrPt Xo c L) (v : L),
    FrMap χ y w → Val hb w v → χ g * v = χ s

theorem exists_rep (hl : EvLaws Xo c) (hA : Atlas h) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    ∃ s, Rep hb y 1 s := by
  let I : Ideal S :=
    { carrier := {g | ∃ s, Rep hb y g s}
      zero_mem' := ⟨0, fun L _ _ χ w v _ _ => by simp⟩
      add_mem' := by
        rintro g g' ⟨s, hs⟩ ⟨s', hs'⟩
        exact ⟨s + s', fun L _ _ χ w v h1 h2 => by
          rw [map_add, map_add, add_mul, hs L χ w v h1 h2, hs' L χ w v h1 h2]⟩
      smul_mem' := by
        rintro r g ⟨s, hs⟩
        exact ⟨r * s, fun L _ _ χ w v h1 h2 => by
          rw [smul_eq_mul, map_mul, map_mul, mul_assoc, hs L χ w v h1 h2]⟩ }
  by_contra hne
  have hI : I ≠ ⊤ := fun hI => hne ((Ideal.eq_top_iff_one I).1 hI)
  obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal I hI
  have := hP.isPrime
  let χ₀ : S →ₐ[c.F] FractionRing (S ⧸ P) :=
    (IsScalarTower.toAlgHom c.F (S ⧸ P) (FractionRing (S ⧸ P))).comp (Ideal.Quotient.mkₐ c.F P)
  obtain ⟨w₀, hw₀⟩ := hl.bc _ _ χ₀ y
  obtain ⟨C, ψ₀, z₀, t₀, h1, h2⟩ := hA _ w₀
  obtain ⟨g, hg, hloc⟩ := C.opn S _ χ₀ y w₀ hw₀ ⟨ψ₀, z₀, t₀, h1, h2⟩
  let lam : S →ₐ[c.F] Localization.Away g := IsScalarTower.toAlgHom c.F S _
  have hu : IsUnit (lam g) := IsLocalization.Away.algebraMap_isUnit g
  obtain ⟨w', hw'⟩ := hl.bc _ _ lam y
  obtain ⟨ψ, z, t, h3, h4⟩ := hloc _ lam hu w' hw'
  have hv : Val hb w' (zchar e t * ψ ⟨_, hb C⟩) := ⟨C, ψ, z, t, h3, h4, rfl⟩
  generalize zchar e t * ψ ⟨_, hb C⟩ = u at hv
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj g u
  have hmem : g ^ (n + 1) ∈ I := by
    refine ⟨g * a, fun L _ _ χ w v h5 h6 => ?_⟩
    by_cases hχ : χ g = 0
    · simp [hχ]
    · let mu : Localization.Away g →ₐ[c.F] L :=
        IsLocalization.liftAlgHom (M := Submonoid.powers g) (f := χ) (by
          rintro ⟨_, k, rfl⟩
          simpa using (IsUnit.mk0 _ hχ).pow k)
      have hmu' : ∀ x, mu (algebraMap S _ x) = χ x := fun x => by
        simp [mu]
      have hmu : mu.comp lam = χ := AlgHom.ext hmu'
      have h7 : FrMap mu w' w := frMap_cancel _ _ _ lam mu y w' w hw' (by rw [hmu]; exact h5)
      have h8 := val_unique hb hl h6 (val_map hb hl mu h7 hv)
      have h9 := congrArg mu ha
      rw [map_mul, map_pow, hmu', hmu'] at h9
      rw [h8, map_mul, map_pow, ← h9]
      ring
  have hgP : g ∈ P := this.mem_of_pow_mem _ (hIP hmem)
  apply hg
  show algebraMap (S ⧸ P) (FractionRing (S ⧸ P)) (Ideal.Quotient.mk P g) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.2 hgP, map_zero]

end Val

theorem exists_sec_of_regular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ h : GenFrEx Xo c, Atlas h → ∀ (a : Ix Dw → ℤ) (b : ∀ Z : Comp Xo c, Om Z), (∀ C : FChart h, zchar a C.t * b C.Z ∈ C.R) → ∃ g ∈ GlobalTheory.AllWt.secZ Xo c a, ∀ Z, evC h Z g = b Z := by
  intro E _ _ _ H Dw l Xo c hl h hA a b hb
  have hred : ∀ p : TRing c.F, IsReduced p.R := fun p => (Ideal.isRadical_iff_quotient_reduced p.I).1 p.rad
  choose g hg using fun (p : TRing c.F) (y : FrPt Xo c p.R) => exists_rep hb hl hA y
  have hg' : ∀ (p : TRing c.F) (y : FrPt Xo c p.R) (L : Type) [Field L] [Algebra c.F L] (χ : p.R →ₐ[c.F] L)
      (w : FrPt Xo c L) (v : L), FrMap χ y w → Val hb w v → χ (g p y) = v := by
    intro p y L _ _ χ w v h1 h2
    rw [← hg p y L χ w v h1 h2, map_one, one_mul]
  refine ⟨g, GlobalTheory.AllWt.mem_secZ.2 ⟨fun p q φ y z hz => ?_, fun p t y y' hy => ?_⟩, fun Z => ?_⟩
  · have := hred q
    refine eq_of_fields (K := c.F) _ _ fun L _ _ χ => ?_
    obtain ⟨w, hw⟩ := hl.bc _ _ χ z
    obtain ⟨v, hv⟩ := val_ex hb hA w
    rw [hg' q z L χ w v hw hv]
    exact (hg' p y L (χ.comp φ) w v (frMap_trans _ _ _ φ χ y z w hz hw) hv).symm
  · have := hred p
    show g p y' = zchar a t * g p y
    refine eq_of_fields (K := c.F) _ _ fun L _ _ χ => ?_
    obtain ⟨w, hw⟩ := hl.bc _ _ χ y
    obtain ⟨w', hw'⟩ := hl.bc _ _ χ y'
    obtain ⟨v, hv⟩ := val_ex hb hA w
    have hv' := val_bor hb (frBorBC _ _ χ t y y' w w' hy hw hw') hv
    rw [hg' p y' L χ w' _ hw' hv', map_mul, hg' p y L χ w v hw hv, zchar_map]
  · have hh := hl.test _ (genFr h Z)
    unfold evC evR evalAt
    rw [dif_pos hh]
    exact hg' _ _ _ _ _ _ hh.choose_spec.choose_spec.choose_spec (val_gen hb hA Z)

theorem exists_secZ_of_regular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (h : GenFrEx Xo c) (w : Ix Dw → ℤ) (b : ∀ Z : Comp Xo c, Om Z), (∀ C : FChart h, ((∏ i, C.t i ^ w i : (Om C.Z)ˣ) : Om C.Z) * b C.Z ∈ C.R) → ∃ f ∈ GlobalTheory.AllWt.secZ Xo c w, ∀ Z, evC h Z f = b Z := by
  intro E _ _ _ H Dw l Xo c h w b hb
  obtain ⟨hL, -, -, hA⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  exact exists_sec_of_regular E H Dw l Xo c hL h (hA h) w b hb

end GlobalTheory.SecGlueInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsBasisNear
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieLocFrame

section Alg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj
open GlobalTheory.LieMet (tanOf isTan_tv isTan_map tan_ext)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {S T U : Type} [CommRing S] [CommRing T] [CommRing U] {x : Sp S ⟶ X} {x' : Sp T ⟶ X} {x'' : Sp U ⟶ X}

def res (ψ : S →+* T) (hx : spMap ψ ≫ x = x') (v : TanM x t.G) : TanM x' t.G := tanOf (isTan_map ψ hx (isTan_tv v))

theorem res_res (ψ : S →+* T) (hx : spMap ψ ≫ x = x') (χ : T →+* U) (hx' : spMap χ ≫ x' = x'') {ω : S →+* U}
    (e : χ.comp ψ = ω) (hx'' : spMap ω ≫ x = x'') (v : TanM x t.G) :
    res χ hx' (res ψ hx v) = res ω hx'' v := by
  subst e
  refine tan_ext ?_
  show spMap (dualMap χ) ≫ spMap (dualMap ψ) ≫ _ = spMap (dualMap (χ.comp ψ)) ≫ _
  rw [← Category.assoc, spMap_comp_spMap]
  congr 2
  exact RingHom.ext fun a => by ext <;> simp [dualMap]

theorem res_sum (ψ : S →+* T) (hx : spMap ψ ≫ x = x') {κ : Type} [Fintype κ] (a : κ → S) (n : κ → TanM x t.G) :
    res ψ hx (∑ k, a k • n k) = ∑ k, ψ (a k) • res ψ hx (n k) := by
  subst hx
  let ρ : overAt (spMap ψ ≫ x) (DualNumber T) ⟶ overAt x (DualNumber S) := Over.homMk (spMap (dualMap ψ)) (by
    show spMap _ ≫ spMap _ ≫ x = spMap _ ≫ spMap _ ≫ x
    rw [← Category.assoc, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap, PullbackSections.dualMap_comp_alg])
  let f : TanM x t.G →+ TanM (spMap ψ ≫ x) t.G :=
    AddMonoidHom.mk' (res ψ rfl) fun a b => tanM_ext (MonObj.comp_mul ρ (tv a) (tv b))
  refine (map_sum f _ _).trans (Finset.sum_congr rfl fun k _ => tan_ext ?_)
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (tv (n k)).left) (FrCov.eps_dual ψ (a k))).trans
    (Category.assoc _ _ _))

def IsBasis {m : ℕ} (v : Fin m → TanM x t.G) : Prop := ∀ n : TanM x t.G, ∃! a : Fin m → S, n = ∑ k, a k • v k

theorem isBasis_iff {m : ℕ} {G' : Over (Sp S)} [GrpObj G'] [IsCommMonObj G'] {Φ : G'.left ⟶ t.G.left}
    (h : IsGrpPullback G' t.G x Φ) {u : Fin m → (epsR S ⟶ G')} {v : Fin m → TanM x t.G}
    (e : ∀ i, pushHom h (epsR S) (u i) = tv (v i)) : IsLieBasis u ↔ IsBasis v := by
  have hs : ∀ a : Fin m → S, tv (∑ i, a i • v i) = combT x (fun i => tv (v i)) a := fun a => by
    classical
    unfold combT
    induction (Finset.univ : Finset (Fin m)) using Finset.induction_on with
    | empty => rfl
    | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, tv_add, ih]; rfl
  have key : ∀ a p n, pushHom h (epsR S) p = tv n → (IsLieComb a u p ↔ n = ∑ k, a k • v k) := fun a p n hp => by
    rw [isLieComb_iff h, hp]
    simp only [e]
    exact ⟨fun q => tanM_ext (q.trans (hs a).symm), fun q => (congrArg tv q).trans (hs a)⟩
  refine ⟨fun hu n => ?_, fun hv => ⟨fun i => (isTangent_iff h _).2 (by rw [e]; exact tv_mem _), fun p hp => ?_⟩⟩
  · obtain ⟨p, hp⟩ := push_surj h (tv n)
    simpa only [key _ p n hp] using hu.2 p ((isTangent_iff h p).2 (by rw [hp]; exact tv_mem n))
  · simpa only [key _ p (mkT _ ((isTangent_iff h p).1 hp)) rfl] using hv (mkT _ ((isTangent_iff h p).1 hp))

theorem IsBasis.res {m : ℕ} {v : Fin m → TanM x t.G} (hv : IsBasis v) (ψ : S →+* T) (hx : spMap ψ ≫ x = x') :
    IsBasis fun i => res ψ hx (v i) := by
  subst hx
  have h₀ := isGrpPullback_pullback t.G x
  have h := isGrpPullback_pullback t.G (spMap ψ ≫ x)
  choose u hu using fun i => push_surj h₀ (tv (v i))
  choose u' hu' using fun i => push_surj h (tv (LieLocFrame.res ψ rfl (v i)))
  have := t.semi.smooth
  have : Smooth ((Over.pullback x).obj t.G).hom := show Smooth (pullback.snd _ _) from inferInstance
  refine (isBasis_iff h hu').1 (Chart.frameLieBCR _ ((isBasis_iff h₀ hu).2 hv) ψ
    (Chart.isGrpPullback_factor x (spMap ψ) h)
    (fun a b v hv => push_inj h (by
      have := smT_add _ _ ((isTangent_iff h v).1 ((Chart.isTan_iff _).1 hv)) a b
      rw [← push_scK h, ← push_scK h, ← push_scK h, ← map_mul] at this
      exact this)) (fun i => (isTangent_iff h _).2 (by rw [hu']; exact tv_mem _)) fun i => ?_)
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.assoc]
    exact (congrArg (fun q => q.left) (hu' i)).trans (congrArg (_ ≫ ·) (congrArg (fun q => q.left) (hu i)).symm)
  · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, Over.w (u' i), Category.assoc]
    refine Eq.trans ?_ (congrArg (_ ≫ ·) (Over.w (u i)).symm)
    exact (spMap_comp_spMap _ _).trans ((congrArg spMap (PullbackSections.dualMap_comp_alg _).symm).trans (spMap_comp_spMap _ _).symm)

variable (t) in

theorem exists_isBasis_near (x : Sp S ⟶ X) {K : Type} [Field K] (φ₀ : S →+* K) :
    ∃ g : S, φ₀ g ≠ 0 ∧ ∀ (T : Type) [CommRing T] (φ : S →+* T) (x' : Sp T ⟶ X), IsUnit (φ g) → spMap φ ≫ x = x' →
      ∃ (n : ℕ) (v : Fin n → TanM x' t.G), IsBasis v := by
  have := t.semi.smooth
  obtain ⟨n, s, hs, hC⟩ := Chart.exists_cover ((Over.pullback x).obj t.G)
  have := RingHom.ker_isPrime φ₀
  obtain ⟨k, hk⟩ := Chart.exists_away_not_mem s hs (RingHom.ker φ₀)
  obtain ⟨C⟩ := hC k
  have h := (isGrpPullback_pullback _ (Chart.fB S (Localization.Away (s k)))).comp (isGrpPullback_pullback t.G x)
  have : Smooth (Chart.Gs ((Over.pullback x).obj t.G) (s k)).hom :=
    MorphismProperty.of_isPullback (P := @Smooth) h.1 ‹_›
  have hk' : IsUnit (φ₀ (s k)) := isUnit_iff_ne_zero.2 hk
  let φ₁ : Localization.Away (s k) →+* K := IsLocalization.Away.lift (s k) hk'
  have := RingHom.ker_isPrime φ₁
  obtain ⟨g, hg, m, v, hv⟩ := Chart.exists_lieBasis_away C (RingHom.ker φ₁)
  have h' := (isGrpPullback_pullback _ (Chart.fB (Localization.Away (s k)) (Localization.Away g))).comp h
  have hb := (isBasis_iff (v := fun i => mkT _ ((isTangent_iff h' _).1 (hv.1 i))) h' fun _ => rfl).1 hv
  obtain ⟨N, a, ha⟩ := IsLocalization.Away.surj (s k) g
  refine ⟨s k * a, ?_, fun T _ φ x' hu hx => ?_⟩
  · have e := congrArg φ₁ ha
    rw [map_mul, map_pow, IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq] at e
    rw [map_mul, ← e]
    exact mul_ne_zero hk (mul_ne_zero hg (pow_ne_zero _ hk))
  · rw [map_mul] at hu
    let ψ₁ : Localization.Away (s k) →+* T := IsLocalization.Away.lift (s k) (isUnit_of_mul_isUnit_left hu)
    have hg' : IsUnit (ψ₁ g) := by
      have e := congrArg ψ₁ ha
      rw [map_mul, IsLocalization.Away.lift_eq] at e
      exact isUnit_of_mul_isUnit_left (e ▸ isUnit_of_mul_isUnit_right hu)
    let ψ₂ : Localization.Away g →+* T := IsLocalization.Away.lift g hg'
    refine ⟨m, _, hb.res ψ₂ ?_⟩
    rw [← hx, ← Category.assoc, ← Category.assoc]
    congr 1
    rw [spMap_comp_spMap, IsLocalization.Away.lift_comp, spMap_comp_spMap, IsLocalization.Away.lift_comp]

end Alg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix
open Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo Formalism.L2.PjFree
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory GlobalTheory.HodgeDomain GlobalTheory.LieMet GlobalTheory.CxPts GlobalTheory.TrueCx
open GlobalTheory.AllWt (Psi)
attribute [local instance] Over.cartesianMonoidalCategory

theorem spMap_res_chart {X Z : Scheme.{0}} (f : Z ⟶ X) {V O : Z.affineOpens} (h : O.1 ≤ V.1) :
    spMap (resG Z h) ≫ LogKS.chart V ≫ f = LogKS.chart O ≫ f := by
  rw [← Category.assoc]
  exact congrArg (· ≫ f) (V.2.map_fromSpec O.2 (homOfLE h).op)

theorem valAt_res {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X Z : Scheme.{0}} {t : SAB H X}
    (f : Z ⟶ X) {k : Type} [CommRing k] {p : Z ⟶ Sp k} {σ : k →+* ℂ} {V O : Z.affineOpens} (h : O.1 ≤ V.1)
    (v : TanM (LogKS.chart V ≫ f) t.G) {y : CxPts p σ} (hO : y ∈ ptsIn p σ O.1) (hV : y ∈ ptsIn p σ V.1) :
    LieMet.valAt f (res (resG Z h) (spMap_res_chart f h) v) hO = LieMet.valAt f v hV :=
  res_res (resG Z h) (spMap_res_chart f h) (evHom hO) (by rw [← Category.assoc, spMap_evHom]) (ω := evHom hV)
    (RingHom.ext fun a => (ev_eq hO _).symm.trans ((ev_res h hO a).trans (ev_eq hV a)))
    (by rw [← Category.assoc, spMap_evHom]) v

theorem exists_local_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X Z : Scheme.{0}) (t : SAB H X) (f : Z ⟶ X) (k : Type) [CommRing k] (p : Z ⟶ Sp k) (σ : k →+* ℂ) (y₀ : CxPts p σ), ∃ (V : Z.affineOpens) (n : ℕ) (v : Fin n → TanM (LogKS.chart V ≫ f) t.G), y₀ ∈ ptsIn p σ V.1 ∧ (∀ (y : CxPts p σ) (hy : y ∈ ptsIn p σ V.1), LinearIndependent ℂ (fun i => valAt f (v i) hy) ∧ Submodule.span ℂ (Set.range fun i => valAt f (v i) hy) = ⊤) ∧ ∀ (W : Z.affineOpens) (w : TanM (LogKS.chart W ≫ f) t.G), ∀ y₁ ∈ ptsIn p σ V.1 ∩ ptsIn p σ W.1, ∃ (O : Z.Opens) (a : Fin n → Γ(Z, O)), y₁ ∈ ptsIn p σ O ∧ ∀ y ∈ ptsIn p σ O, ∀ (hy : y ∈ ptsIn p σ V.1) (hy' : y ∈ ptsIn p σ W.1), valAt f w hy' = ∑ i, ev p σ O (a i) y • valAt f (v i) hy := by
  intro E _ _ _ H X Z t f k _ p σ y₀
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (X := Z) (U := ⊤)
    (x := y₀.1 (IsLocalRing.closedPoint ℂ)) trivial
  have h₀ : y₀ ∈ ptsIn p σ U := mem_ptsIn.2 hyU
  obtain ⟨g, hg, hb⟩ := exists_isBasis_near t (LogKS.chart ⟨U, hU⟩ ≫ f) (evHom h₀)
  let V : Z.affineOpens := ⟨Z.basicOpen g, hU.basicOpen g⟩
  have hVU : V.1 ≤ U := Z.basicOpen_le g
  obtain ⟨n, v, hv⟩ := hb Γ(Z, V.1) (resG Z hVU) (LogKS.chart V ≫ f) (Z.toRingedSpace.isUnit_res_basicOpen g)
    (spMap_res_chart f (V := ⟨U, hU⟩) hVU)
  refine ⟨V, n, v, (mem_ptsIn_basicOpen h₀ g).2 (by rwa [ev_eq h₀]), fun y hy => ?_, fun W w y₁ hy₁ => ?_⟩
  · have hy' : IsBasis fun i => LieMet.valAt f (v i) hy :=
      hv.res (evHom hy) (by rw [← Category.assoc, spMap_evHom])
    refine ⟨Fintype.linearIndependent_iff.2 fun a ha =>
      congrFun ((hy' 0).unique (y₁ := a) (y₂ := 0) ha.symm (by simp)), top_unique fun w _ => ?_⟩
    obtain ⟨a, ha, -⟩ := hy' w
    exact ha ▸ Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · obtain ⟨O, hO, hyO, hle⟩ := exists_isAffineOpen_mem_and_subset (X := Z) (U := V.1 ⊓ W.1)
      (x := y₁.1 (IsLocalRing.closedPoint ℂ)) ⟨mem_ptsIn.1 hy₁.1, mem_ptsIn.1 hy₁.2⟩
    have hOV : O ≤ V.1 := fun z hz => (hle hz).1
    have hOW : O ≤ W.1 := fun z hz => (hle hz).2
    obtain ⟨a, ha, -⟩ := hv.res _ (spMap_res_chart f (O := ⟨O, hO⟩) hOV)
      (res _ (spMap_res_chart f (O := ⟨O, hO⟩) hOW) w)
    refine ⟨O, a, mem_ptsIn.2 hyO, fun y hyO' hy hy' => ?_⟩
    rw [← valAt_res f (O := ⟨O, hO⟩) hOW w hyO' hy', ha]
    refine (res_sum (evHom hyO') (by rw [← Category.assoc, spMap_evHom (V := ⟨O, hO⟩)]) a _).trans
      (Finset.sum_congr rfl fun i _ => ?_)
    rw [ev_eq hyO', ← valAt_res f (O := ⟨O, hO⟩) hOV (v i) hyO' hy]
    rfl

end GlobalTheory.LieLocFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocExtANat
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM

namespace GlobalTheory.LocM

theorem exists_loc_extA_nat :
    ∀ (D : D7) (N j p : ℕ), ∃ L : ModuliIntegralCharts.Loc D N j p, Nonempty (ModuliIntegralCharts.ExtA D L) :=
  fun D N j p =>
    ⟨Formalism.MainNotions.DIV.Inh.LocalProvisionModel.locM D N j p (Formalism.MainNotions.DIV.Inh.LocalProvisionModel.mpTrivialAb D p (Formalism.MainNotions.DIV.Inh.nonempty_coefficient_field p).some),
      ⟨Formalism.MainNotions.DIV.Inh.LocalProvisionModel.extM D N j p (Formalism.MainNotions.DIV.Inh.LocalProvisionModel.mpTrivialAb D p (Formalism.MainNotions.DIV.Inh.nonempty_coefficient_field p).some)⟩⟩

end GlobalTheory.LocM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsToricTorsionSectionsUniformisationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_toric_torsion_sections_uniformisation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) [CharZero R], AdmBase R (maximalIdeal R) → ∀ k : ℕ, 1 ≤ k →
    ∃ s : ∀ (A : Type) [CommRing A] (a : R →+* A) (τ : Multiplicative P.D.toPre.X →* Aˣ), τ ^ k = 1 → (Over.mk (spMap a) ⟶ t.G),
      (∀ (A : Type) [CommRing A] (a : R →+* A) τ h, s A a τ h ^ k = 1) ∧
      (∀ (A A' : Type) [CommRing A] [CommRing A'] (a : R →+* A) (a' : R →+* A') (f : A →+* A') τ h τ' h',
        a' = f.comp a → (∀ χ, (τ' χ : A') = f (τ χ : A)) → (s A' a' τ' h').left = spMap f ≫ (s A a τ h).left) ∧
      (∀ (A A' : Type) [CommRing A] [CommRing A'] (a : R →+* A) (ha : ∀ x ∈ maximalIdeal R, a x = 0) (a' : R →+* A') (f : A →+* A')
        (t₀ : SAB H (Sp A)) (m₀ : SABMap t₀ t (spMap a)) τ h (z : Over.mk (spMap f) ⟶ splitTorus (Sp A) P.D.toPre.X),
        a' = f.comp a → (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ))) →
        (s A' a' τ h).left = (z ≫ GlobalTheory.TorusPart.PELUnif.torus P ha m₀).left ≫ m₀.φ) ∧
      ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (a : R →+* F) τ h (q : QkPt P.D.toPre F k),
        a = (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)) → q.y = 0 → GlobalTheory.UT.IsTor τ q.g →
        GlobalTheory.FlatTors.IsImage P F k q (s F a τ h).left := by
  first | exact @GlobalTheory.ToricTorsionSec.main | exact GlobalTheory.ToricTorsionSec.main | (intros; apply GlobalTheory.ToricTorsionSec.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRelativeTangentTopChernNeZero
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.GoodMetric

theorem rootDiscr_ne_zero : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ), rootDiscr m ≠ 0 := by
  intro ι _ m
  unfold rootDiscr
  refine Finset.prod_ne_zero_iff.mpr fun τ _ => Finset.prod_ne_zero_iff.mpr fun j _ =>
    Finset.prod_ne_zero_iff.mpr fun i hi => ?_
  rw [sub_ne_zero]
  intro h
  have h2 := X_injective (σ := Root m) (R := ℝ) h
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at h2
  exact (Finset.mem_Iio.mp hi).ne h2.symm

end GlobalTheory.GoodMetric
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlatOfQuasiFiniteOfFlatFibresStatement
section
open AlgebraicGeometry CategoryTheory Limits MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_of_quasiFinite_of_flat_fibres' : ∀ (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] [Algebra.FinitePresentation A B] [Algebra.QuasiFinite A B] [Module.Flat R B], (∀ (k C : Type) [Field k] [CommRing C] [Algebra A C] (t : R →+* k) (h : k →+* C), (algebraMap A C).comp (algebraMap R A) = h.comp t → Module.Flat C (C ⊗[A] B)) → Module.Flat A B := by
  first | exact @GlobalTheory.flat_of_quasiFinite_of_flat_fibres | exact GlobalTheory.flat_of_quasiFinite_of_flat_fibres | (intros; apply GlobalTheory.flat_of_quasiFinite_of_flat_fibres <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameBaseChangeRingHomStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFrame_baseChange_ringHom : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (X : Scheme.{0}) (t : SAB H X) (R S : Type) [CommRing R] [CommRing S] (f : c.F →+* R) (φ : R →+* S) (x : Sp R ⟶ X) (u : Vecs Dw t R), GlobalTheory.LocM.IsFrame t f x u → GlobalTheory.LocM.IsFrame t (φ.comp f) (spMap φ ≫ x) (u.bc φ) := by
  first | exact @GlobalTheory.LocM.isFrame_bc | exact GlobalTheory.LocM.isFrame_bc | (intros; apply GlobalTheory.LocM.isFrame_bc <;> assumption)
end


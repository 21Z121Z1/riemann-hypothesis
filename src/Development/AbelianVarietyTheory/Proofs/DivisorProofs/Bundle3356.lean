import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2522
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2486
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2469
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3325
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2437
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2996
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3346
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3345
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3351
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3347
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0173
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0131
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3253
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3262
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3313
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3280
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3116
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3137
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3349
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2213
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3348
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSetupTowerLargeRatio
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep.TowerLarge

theorem isDiagEnd_of_isAct {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}}
    {i : F.X ⟶ Z} (X₁ : Setup F W i) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (h : IsAct X₁ act) :
    IsDiagEnd F W X₁.ρ.P X₁.u act := by
  obtain ⟨c, hc, pr, hpr, hu, hL, hact⟩ := h
  exact ⟨c, hc, pr, hpr, hu, hL, fun E a => by simpa [List.ofFn_eq_map] using hact E a⟩

theorem isAct_of_isDiagEnd {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}}
    {i : F.X ⟶ Z} (X₁ : Setup F W i) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A))
    (h : IsDiagEnd F W X₁.ρ.P X₁.u act) : IsAct X₁ act := by
  obtain ⟨c, hc, pr, hpr, hu, hL, hact⟩ := h
  exact ⟨c, hc, pr, hpr, hu, hL, fun E a => by simpa [List.ofFn_eq_map] using hact E a⟩

theorem lbIso_pull_comp' {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {a : Y ⟶ X} (h : LBIso M (L.pull a)) (j : Z ⟶ Y)
    {a' : Z ⟶ X} (e : a' = j ≫ a) : LBIso (M.pull j) (L.pull a') :=
  LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull M j j rfl)
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullSame L _ (fun _ => a) _ j fun _ => e) h

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem exists_tower_ge : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ N₀ : ℕ, ∃ 𝔗 : Tower X₁ act, N₀ ≤ 𝔗.X₂.S.r * 𝔗.X₂.S.N := by
  intro g _ n _ _ F Z z i _ _ _ _ _ W _ _ X₁ _ act hact N₀
  have hε₁ := isDiagEnd_of_isAct X₁ act hact
  have hℓp : X₁.ρ.n.Prime := X₁.ρ.n_prime
  have hℓ2 : 2 ≤ X₁.ρ.n := hℓp.two_le
  obtain ⟨j₁, hj₁, hr⟩ := X₁.ρ.r_eq
  have hL₁ : X₁.S.r * X₁.S.N = X₁.ρ.n ^ (j₁ + 2 * X₁.ρ.k) := by
    rw [hr, X₁.ρ.N_eq, ← pow_mul, ← pow_add, mul_comm X₁.ρ.k 2]
  obtain ⟨k, j₀, hk, hBk, hj₀, big⟩ := GSetup.exists_big_ge X₁.ρ.P.g X₁.ρ.n hℓ2 N₀
  have hun1 : IsUnit (X₁.ρ.n : X₁.o₁) := by
    have hd : X₁.ρ.n ∣ X₁.S.r * X₁.S.N := by
      rw [hL₁]; exact dvd_pow_self _ (by omega)
    exact isUnit_of_dvd_unit (Nat.cast_dvd_cast hd) X₁.S.unit
  haveI : CharZero X₁.Ω₁ := ArithBase.char (o := X₁.o₁)
  have hM : 0 < X₁.S.r * X₁.S.N := by rw [hL₁]; exact pow_pos hℓp.pos _
  have hζ₀ : ∃ ζ₀ : X₁.Ω₁, IsPrimitiveRoot ζ₀ (X₁.S.r * X₁.S.N) :=
    ⟨_, (X₁.S.prim.pow (by positivity) (sq _)).map_of_injective (ArithBase.inj (o := X₁.o₁) (Ω := X₁.Ω₁))⟩
  have htors : ∀ (E : Type) [Field E] [IsAlgClosed E] (x : Sp E ⟶ Sp X₁.S.R) (z : Over.mk x ⟶ X₁.ρ.P.A),
      z ^ (X₁.S.r * X₁.S.N) = 1 → ∃ y : baseOver (Sp X₁.S.R) ⟶ X₁.ρ.P.A,
        (Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp X₁.S.R)) ≫ y = z := by
    intro E _ _ x z hz
    obtain ⟨a, ha, -⟩ := X₁.ρ.pt_bij E x z hz
    exact ⟨_, ha⟩
  set j := j₀ + (j₁ + 2 * X₁.ρ.k) with hj
  set K := (X₁.ρ.n ^ j * (X₁.ρ.n ^ k) ^ 2) ^ 2 with hK
  have hKpos : 0 < K := by have := hℓp.pos; positivity
  obtain ⟨Ω₂, _, _, Q, φQ, ζ, fd, gal, deg, hζ, hQg, hQpb, hQlb, ⟨levQ⟩⟩ :=
    GlobalTheory.T.exists_primePower_galois_ext_symplecticLevel X₁.S.R.val.toRingHom X₁.ρ.P X₁.ρ.n (X₁.S.r * X₁.S.N) K hℓp hM
      (by rw [hL₁]; exact dvd_pow_self _ (by omega)) ⟨2 * (j + 2 * k), by rw [hK]; ring⟩ hζ₀ htors
  haveI := fd
  obtain ⟨o₂, _, _, _, κ, ze, hκ, hc, hze⟩ := GlobalTheory.Poinc.exists_arithBase_rootOfUnity (o₁ := X₁.o₁) (Ω₁ := X₁.Ω₁) Ω₂ K ζ hKpos hζ
  obtain ⟨R, h, hfg, hfr, hh, hfin, hic, hstab⟩ := GlobalTheory.T.exists_integralClosure_finite_galoisStable_thetaRing X₁.S.R X₁.S.fg X₁.S.frac κ hκ hc
  haveI := GlobalTheory.ThetaReal.isNoetherian_of_fg hfg
  haveI := GlobalTheory.GenSpread.isFractionRing_of_forall_div hfr
  have hun2 : IsUnit (X₁.ρ.n : o₂) := by simpa using hun1.map κ
  have hKunit : IsUnit (K : R) := by
    have := (hun2.map (algebraMap o₂ R))
    rw [map_natCast] at this
    rw [hK]; push_cast
    exact ((this.pow _).mul ((this.pow _).pow _)).pow _
  let zeR : (↥R)ˣ := Units.map (algebraMap o₂ R).toMonoidHom ze
  have hzeR : Units.map (algebraMap R Ω₂).toMonoidHom zeR = ζ := by
    rw [← hze]; ext; rfl
  have hQpb' : IsGrpPullback Q.A X₁.ρ.P.A (spMap ((algebraMap R Ω₂).comp h)) φQ := by
    have e : (algebraMap R Ω₂).comp h = (algebraMap X₁.Ω₁ Ω₂).comp X₁.S.R.val.toRingHom := RingHom.ext hh
    rw [e]; exact hQpb
  obtain ⟨P, ψ, hPg, hpb, hlb, ⟨lev⟩⟩ := GlobalTheory.T.symplecticLevel_extends_noetherian_normalDomain X₁.ρ.P R Ω₂ h Q φQ K zeR hKpos hKunit hQg hQpb' hQlb
    ⟨by rw [hzeR]; exact levQ⟩
  have hS := GlobalTheory.Poinc.hypS_polAV_pullback X₁.ρ.P P (spMap h) ψ hpb hlb X₁.ρ.hypS
  obtain ⟨th, hth⟩ := GlobalTheory.T.exists_polarization_sectionBasis_pullback_affine X₁.ρ.P P h ψ hpb hlb X₁.ρ.th₁ X₁.ρ.th₁_basis
  obtain ⟨S₂, ρ₂, hR, φ₂, hSR, -, -, hN₂, hr₂, hg₂, hpb₂, hlb₂⟩ :=
    GlobalTheory.T.exists_realisedThetaSystem_of_universalSectionBasis o₂ Ω₂ R hfg hfr P X₁.ρ.n k j ze hℓp X₁.ρ.n_odd hk (by omega) hun2 hS th hth lev
  set om : X₁.S.R →+* S₂.R := (Subalgebra.inclusion hR).toRingHom.comp h with hom
  have hval : ∀ a, ((om a : S₂.R) : Ω₂) = algebraMap X₁.Ω₁ Ω₂ a := fun a => hh a
  have hcart : IsGrpPullback ρ₂.P.A X₁.ρ.P.A (spMap om) (φ₂ ≫ ψ) := by
    rw [hom, ← spMap_comp']
    exact hpb₂.comp hpb
  have hlbc : LBIso ρ₂.P.L (X₁.ρ.P.L.pull (φ₂ ≫ ψ)) :=
    LBIso.trans ρ₂.P.isLB (pull_isLB P.isLB _) (pull_isLB X₁.ρ.P.isLB _) hlb₂ (lbIso_pull_comp' hlb φ₂ rfl)
  obtain ⟨ε₂, hε₂, hεc⟩ := GlobalTheory.Poinc.isDiagEnd_pullback F W X₁.ρ.P ρ₂.P X₁.u (spMap om) (φ₂ ≫ ψ) act hε₁ hcart hlbc
  have hsharp : SharpOver F W ρ₂.P (spMap om ≫ X₁.u) := by
    obtain ⟨c, hc₁, pr, hpr, hun, hLc, -⟩ := hε₂
    exact ⟨c, hc₁, pr, hpr, hun, hLc⟩
  have key : spMap S₂.R.val.toRingHom ≫ spMap om = spMap (algebraMap X₁.Ω₁ Ω₂) ≫ spMap X₁.S.R.val.toRingHom := by
    rw [spMap_comp', spMap_comp']
    congr 1
    ext a
    exact hval a
  have hgen : ∀ w, (spMap S₂.R.val.toRingHom ≫ spMap om ≫ X₁.u) w ∈ genericPoints F.X := by
    intro w
    rw [← Category.assoc, key, Category.assoc, Scheme.Hom.comp_apply]
    exact X₁.gen _
  obtain ⟨M₂, q, hMn, hq, hqgen⟩ := GlobalTheory.Poinc.Setup.exists_model_of_finiteDimensional X₁ o₂ Ω₂ κ hκ hc
  haveI := hq
  haveI := X₁.fin
  have hcomp : M₂.pt ≫ q ≫ X₁.π = spMap S₂.R.val.toRingHom ≫ (spMap om ≫ X₁.u) ≫ i := by
    rw [← Category.assoc, hqgen, Category.assoc, X₁.comp, Category.assoc, ← Category.assoc (spMap S₂.R.val.toRingHom),
      key, Category.assoc]
  have hbase : spMap S₂.R.val.toRingHom ≫ (spMap om ≫ X₁.u) ≫ F.s =
      spMap ((algebraMap o₂ Ω₂).comp (κ.comp X₁.κ)) := by
    rw [← Category.assoc, ← Category.assoc, key, Category.assoc, Category.assoc, X₁.base, spMap_comp', ← RingHom.comp_assoc, ← hc]
  have hbig : S₂.Big := big j (by omega) o₂ Ω₂ S₂ (hg₂.trans hPg) hN₂ hr₂
  let X₂ : Setup F W i := Setup.mk o₂ Ω₂ S₂ ρ₂ hbig (spMap om ≫ X₁.u) hsharp hgen M₂ hMn (q ≫ X₁.π) inferInstance hcomp
    X₁.one_le X₁.three_le X₁.odd X₁.z X₁.proj X₁.normalZ X₁.imm X₁.thetaSetup_structureMap_comp X₁.dense X₁.e8 X₁.thetaInt (κ.comp X₁.κ) hbase
  set d := X₁.ρ.n ^ (j₀ + 2 * k) with hd
  have hlev : S₂.r * S₂.N = X₁.S.r * X₁.S.N * d := by
    rw [hr₂, hN₂, hL₁, hd, hj, ← pow_mul, ← pow_add, ← pow_add, mul_comm k 2]
    ring_nf
  obtain ⟨lam, hlam, hlamr⟩ := GlobalTheory.T.exists_thetaRealisation_labels_of_grpPullback X₁.S S₂ X₁.ρ ρ₂ om (φ₂ ≫ ψ) d hcart hlev
  have hRS : ∀ x : Ω₂, x ∈ S₂.R ↔ x ∈ R := fun x => by rw [hSR]
  let sR : (Ω₂ ≃ₐ[X₁.Ω₁] Ω₂) → (S₂.R →+* S₂.R) := fun σ =>
    RingHom.codRestrict (((σ : Ω₂ ≃+* Ω₂) : Ω₂ →+* Ω₂).comp S₂.R.val.toRingHom) S₂.R
      (fun x => (hRS _).2 (hstab σ x ((hRS _).1 x.2)))
  have hsR : ∀ σ, (sR σ).comp om = om := fun σ => RingHom.ext fun a => Subtype.ext
    ((congrArg σ (hval a)).trans ((σ.commutes _).trans (hval a).symm))
  choose gl hgl using fun σ => GlobalTheory.T.exists_thetaRealisation_label_perm_of_ringEndo X₁.S S₂ X₁.ρ ρ₂ om (φ₂ ≫ ψ) hcart (sR σ) (hsR σ)
  have hgll : ∀ σ a, gl σ (lam a) = lam a := fun σ a => GlobalTheory.T.thetaRealisation_labels_injective_of_grpPullback S₂ ρ₂ X₁.ρ.P.A (spMap om) (φ₂ ≫ ψ) hcart _ _ (by
      rw [hgl, hlam, ← Category.assoc, spMap_comp', hsR])
  let 𝔗 : Tower X₁ act :=
    { X₂ := X₂
      act₂ := ε₂
      isAct := isAct_of_isDiagEnd X₂ ε₂ hε₂
      alg := inferInstance
      fd := fd
      gal := gal
      deg := deg
      d := d
      lev := hlev
      om := om
      om_eq := hval
      om_fin := RingHom.Finite.comp (RingHom.Finite.of_surjective _ fun x => ⟨⟨x.1, (hRS _).1 x.2⟩, rfl⟩) hfin
      sR := sR
      sR_eq := fun σ a => rfl
      p := q
      p_fin := hq
      p_pt := hqgen
      p_π := rfl
      φ := φ₂ ≫ ψ
      cart := hcart
      lb := hlbc
      act_eq := hεc
      lam := lam
      lam_pt := hlam
      lam_range := hlamr
      gl := gl
      gl_pt := hgl
      gl_lam := hgll }
  refine ⟨𝔗, ?_⟩
  show N₀ ≤ S₂.r * S₂.N
  rw [hN₂, hr₂]
  exact hBk.trans (Nat.le_mul_of_pos_left _ (by have := hℓp.pos; positivity))

end GlobalTheory.Poinc.Sep.TowerLarge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleChernIntegralPullFirst
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

namespace GlobalTheory.LogSinElim

section Alg

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) {ι : Type} (w : ι → A.Pt → Ev n)

theorem evalF_add' (P Q : MvPolynomial ι ℝ) : evalF A w (P + Q) = evalF A w P + evalF A w Q := by
  funext x
  simp only [evalF, fld, map_add, Pi.add_apply, AddMemClass.coe_add]

theorem evalF_mul' (P Q : MvPolynomial ι ℝ) : evalF A w (P * Q) = evalF A w P * evalF A w Q := by
  funext x
  simp only [evalF, fld, map_mul, Pi.mul_apply, MulMemClass.coe_mul]

theorem evalF_sub' (P Q : MvPolynomial ι ℝ) : evalF A w (P - Q) = evalF A w P - evalF A w Q := by
  funext x
  simp only [evalF, fld, map_sub, Pi.sub_apply, AddSubgroupClass.coe_sub]

theorem evalF_X' (i : ι) : evalF A w (X i) = fld A (w i) := by
  funext x
  simp [evalF, fld]

theorem evalF_C' (r : ℝ) : evalF A w (C r) = (r : ℂ) • (1 : A.Fld) := by
  funext x
  simp [evalF, fld, Algebra.algebraMap_eq_smul_one]
  rfl

theorem evalF_aeval_self (s : ι → MvPolynomial ι ℝ) (hs : ∀ i, fld A (w i) = evalF A w (s i))
    (P : MvPolynomial ι ℝ) : evalF A w P = evalF A w (aeval s P) := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [evalF_C']
  | add P Q hP hQ => rw [map_add, evalF_add', evalF_add', hP, hQ]
  | mul_X P i hP => rw [map_mul, evalF_mul', evalF_mul', hP, aeval_X, evalF_X', hs]

end Alg

end GlobalTheory.LogSinElim

namespace GlobalTheory.LogSinElim

section Pull

variable {M M' : Type} [TopologicalSpace M] [TopologicalSpace M'] {n n' : ℕ} (A : HolAtlas M n) (A' : HolAtlas M' n')
  {ι κ : Type} (w : ι → A.Pt → Ev n) (w' : κ → A'.Pt → Ev n')

theorem pullback_evalF (f : M' → M) (hf : A.IsHolo A' f) (s : ι → MvPolynomial κ ℝ)
    (hs : ∀ i, A.pullback A' f (fld A (w i)) = evalF A' w' (s i)) (P : MvPolynomial ι ℝ) :
    A.pullback A' f (evalF A w P) = evalF A' w' (aeval s P) := by
  have hp := ((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).2.2.2.2 M' n' A' f hf)
  induction P using MvPolynomial.induction_on with
  | C r => rw [evalF_C', aeval_C, algebraMap_eq, evalF_C', (hp.2 (r : ℂ) 1 1).2.2.1, hp.1]
  | add P Q hP hQ => rw [evalF_add', (hp.2 1 _ _).1, hP, hQ, map_add, evalF_add']
  | mul_X P i hP => rw [evalF_mul', (hp.2 1 _ _).2.1, hP, evalF_X', hs, map_mul, aeval_X, evalF_mul']

end Pull

def subQ : Fin 5 → MvPolynomial (Fin 5) ℝ := ![X 0, X 3 + X 4 - X 0, X 2, X 3, X 4]

def subB : Fin 5 → MvPolynomial (Fin 5) ℝ := ![X 4, X 3, X 2, X 3, X 4]

theorem dvd_aeval_sub (P : MvPolynomial (Fin 5) ℝ) : (X 4 - X 0 : MvPolynomial (Fin 5) ℝ) ∣ aeval subQ P - aeval subB P := by
  induction P using MvPolynomial.induction_on with
  | C r => simp
  | add P Q hP hQ =>
    rw [map_add, map_add, add_sub_add_comm]
    exact dvd_add hP hQ
  | mul_X P i hP =>
    have hi : (X 4 - X 0 : MvPolynomial (Fin 5) ℝ) ∣ subQ i - subB i := by
      fin_cases i
      · exact ⟨-1, by simp [subQ, subB]⟩
      · exact ⟨1, by simp [subQ, subB]; ring⟩
      · exact ⟨0, by simp [subQ, subB]⟩
      · exact ⟨0, by simp [subQ, subB]⟩
      · exact ⟨0, by simp [subQ, subB]⟩
    rw [map_mul, map_mul, aeval_X, aeval_X,
      show aeval subQ P * subQ i - aeval subB P * subB i =
        (aeval subQ P - aeval subB P) * subQ i + aeval subB P * (subQ i - subB i) by ring]
    exact dvd_add (dvd_mul_of_dvd_left hP _) (dvd_mul_of_dvd_right hi _)

end GlobalTheory.LogSinElim

namespace GlobalTheory.LogSinElim

theorem evalF_one' {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) {ι : Type} (w : ι → A.Pt → Ev n) :
    evalF A w 1 = 1 := by
  funext x
  simp [evalF, fld]

theorem logSin_elim : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    ∀ K : MvPolynomial (Fin 5) ℝ, K.IsHomogeneous d →
      wInt (hY.atlas σ) (fun y => Real.log (1 - v y) / 2) (evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) ((X 0 - X 3) * K)) =
        1 / 2 * ((hY.atlas σ).integral (fld (hY.atlas σ) (omF hY σ (h.pull π w) fl) * evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) K) - (hY.atlas σ).integral (pullF hB hY σ π w (fld (hB.atlas σ) (omF hB σ h flB)) * evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) K)) := by
  intro k _ B Y _ _ q p d hB hY π w E h H flB fl hfl A σ v hv K _hK
  haveI : CompactSpace (CxPts p σ) := CxPts.compactSpace σ hY.isProjOver
  haveI : T2Space (CxPts p σ) := CxPts.t2Space_cxPts_of_isProjOver σ hY.isProjOver
  haveI : SecondCountableTopology (CxPts p σ) := CxPts.secondCountableTopology_of_isProjOver σ hY.isProjOver
  obtain ⟨hLY, hEY, -⟩ := GlobalTheory.T.firstChern_form_properties k Y p (d + 1) hY σ
  obtain ⟨hLB, hEB, hPB⟩ := GlobalTheory.T.firstChern_form_properties k B q d hB σ
  obtain ⟨hol, hc1pull, hEpull⟩ := hPB Y p (d + 1) hY π w
  have hrel := (hEpull E h H flB fl).2
  have calcY := GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ (d + 1) (hY.atlas σ)
  have calcB := GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ d (hB.atlas σ)
  have lin := GlobalTheory.T.holAtlas_topFormIntegral_finite_additive_homogeneous _ (d + 1) (hY.atlas σ)
  obtain ⟨hint, hfib⟩ := GlobalTheory.T.flag_bundle_chern_integral_pull_fourth k B Y q p d hB hY π w E h H flB fl hfl A σ v hv
  have hpl := GlobalTheory.T.flag_bundle_chern_integral_pull_fifth k B Y q p d hB hY π w E h H flB fl hfl A σ v hv
  have hglob := GlobalTheory.T.flag_bundle_chern_integral_pull_third k B Y q p d hB hY π w E h H flB fl hfl A σ
  have hpb := calcB.2.2.2.2 _ (d + 1) (hY.atlas σ) _ hol
  set w5 : Fin 5 → (hY.atlas σ).Pt → Ev (d + 1) := fun i => c1F hY σ (fam5 π w H flB fl A i) with hw5
  let wB : Fin 5 → (hB.atlas σ).Pt → Ev d := ![c1F hB σ (VMetric.grLB flB 1 H), c1F hB σ (VMetric.grLB flB 0 H),
    c1F hB σ A, c1F hB σ (VMetric.grLB flB 0 H), c1F hB σ (VMetric.grLB flB 1 H)]
  have f5 : ∀ i, (hY.atlas σ).IsForm (fld _ (w5 i)) := fun i => (hLY (fam5 π w H flB fl A i) (fam5 π w H flB fl A i)).1.1
  have fB : ∀ i, (hB.atlas σ).IsForm (fld _ (wB i)) := by
    intro i
    fin_cases i
    exacts [(hLB _ A).1.1, (hLB _ A).1.1, (hLB _ A).1.1, (hLB _ A).1.1, (hLB _ A).1.1]
  have ev5 : ∀ P, (hY.atlas σ).IsForm (evalF _ w5 P) := fun P => (calcY.2.2.2.1 (Fin 5) w5 P f5).1
  have evB : ∀ P, (hB.atlas σ).IsForm (evalF _ wB P) := fun P => (calcB.2.2.2.1 (Fin 5) wB P fB).1
  have hωY : (hY.atlas σ).IsForm (fld _ (omF hY σ (h.pull π w) fl)) := (hEY _ (h.pull π w) (H.pull π w) fl fl).1.1
  have hωB : (hB.atlas σ).IsForm (fld _ (omF hB σ h flB)) := (hEB E h H flB flB).1.1
  have hmulY : ∀ α β, (hY.atlas σ).IsForm α → (hY.atlas σ).IsForm β → (hY.atlas σ).IsForm (α * β) :=
    fun α β hα hβ => (calcY.2.1 1 α β hα hβ).2.1
  have hmulB : ∀ α β, (hB.atlas σ).IsForm α → (hB.atlas σ).IsForm β → (hB.atlas σ).IsForm (α * β) :=
    fun α β hα hβ => (calcB.2.1 1 α β hα hβ).2.1
  have hpω : (hY.atlas σ).IsForm (pullF hB hY σ π w (fld _ (omF hB σ h flB))) := ((hpb.2 1 _ 1).2.2.2 hωB).1
  have intAdd : ∀ α β, (hY.atlas σ).IsForm α → (hY.atlas σ).IsForm β →
      (hY.atlas σ).integral (α + β) = (hY.atlas σ).integral α + (hY.atlas σ).integral β := by
    intro α β hα hβ
    rw [← wInt_one, ← wInt_one, ← wInt_one]
    exact (lin.2.1 (fun _ => 1) α β hα hβ (fun ε => by haveI := lin.1 α hα ε; exact integrable_const _)
      (fun ε => by haveI := lin.1 β hβ ε; exact integrable_const _)).2

  have hrel' : ∀ x, w5 1 x = w5 3 x + w5 4 x - w5 0 x := fun x => by
    have e : w5 0 x + w5 1 x = w5 3 x + w5 4 x := congrFun hrel x
    exact eq_sub_of_add_eq' e
  have hsQ : ∀ i, fld _ (w5 i) = evalF (hY.atlas σ) w5 (subQ i) := by
    intro i
    fin_cases i
    · exact (evalF_X' _ w5 0).symm
    · show fld _ (w5 1) = evalF _ w5 (X 3 + X 4 - X 0)
      rw [evalF_sub', evalF_add', evalF_X', evalF_X', evalF_X']
      funext x
      simp only [fld, Pi.add_apply, Pi.sub_apply, hrel' x, AddSubgroupClass.coe_sub, AddMemClass.coe_add]
    · exact (evalF_X' _ w5 2).symm
    · exact (evalF_X' _ w5 3).symm
    · exact (evalF_X' _ w5 4).symm
  have hsB : ∀ i, pullF hB hY σ π w (fld _ (wB i)) = evalF (hY.atlas σ) w5 (subB i) := by
    intro i
    fin_cases i
    · exact (hc1pull (VMetric.grLB flB 1 H)).symm.trans (evalF_X' _ w5 4).symm
    · exact (hc1pull (VMetric.grLB flB 0 H)).symm.trans (evalF_X' _ w5 3).symm
    · exact (hc1pull A).symm.trans (evalF_X' _ w5 2).symm
    · exact (hc1pull (VMetric.grLB flB 0 H)).symm.trans (evalF_X' _ w5 3).symm
    · exact (hc1pull (VMetric.grLB flB 1 H)).symm.trans (evalF_X' _ w5 4).symm
  have hφ : pullF hB hY σ π w (evalF _ wB K) = evalF _ w5 (aeval subB K) :=
    pullback_evalF _ _ wB w5 _ hol subB hsB K

  obtain ⟨K1, hK1⟩ := dvd_aeval_sub K
  have hKs : evalF _ w5 K = evalF _ w5 ((X 4 - X 0) * K1) + evalF _ w5 (aeval subB K) := by
    rw [evalF_aeval_self _ w5 subQ hsQ K, ← evalF_add', ← hK1, sub_add_cancel]
  have hXK : evalF _ w5 ((X 0 - X 3) * K) =
      evalF _ w5 ((X 0 - X 3) * ((X 4 - X 0) * K1)) + evalF _ w5 (X 0 - X 3) * pullF hB hY σ π w (evalF _ wB K) := by
    rw [evalF_mul', hKs, mul_add, ← evalF_mul', hφ]

  have e1 := hfib _ (evB K)
  have e2 := (hglob _ (evB K) 0).2
  have e3 := (hglob _ (hmulB _ _ hωB (evB K)) 0).1
  have hs0 : hs 0 = 1 := by simp [hs]
  rw [hs0, map_one, evalF_one', pow_zero, mul_one, one_mul] at e2
  have hpm : ∀ α β, pullF hB hY σ π w (α * β) = pullF hB hY σ π w α * pullF hB hY σ π w β :=
    fun α β => (hpb.2 1 α β).2.1
  rw [pow_zero, one_mul, hpm] at e3
  norm_num at e2
  have hpF : (hY.atlas σ).IsForm (pullF hB hY σ π w (evalF _ wB K)) := ((hpb.2 1 _ 1).2.2.2 (evB K)).1
  have eA := (lin.2.1 (fun y => Real.log (1 - v y) / 2) _ _ (ev5 ((X 0 - X 3) * ((X 4 - X 0) * K1)))
    (hmulY _ _ (ev5 (X 0 - X 3)) hpF) (hint _ (ev5 _))
    (hint _ (hmulY _ _ (ev5 (X 0 - X 3)) hpF))).2
  have eK1 := hpl K1
  rw [hXK, eA, eK1, hKs, mul_add, mul_add, intAdd _ _ (hmulY _ _ hωY (ev5 _)) (hmulY _ _ hωY (ev5 _)),
    intAdd _ _ (hmulY _ _ hpω (ev5 _)) (hmulY _ _ hpω (ev5 _)), ← hφ, e1, e2, e3]
  ring

end GlobalTheory.LogSinElim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratedBundlesReciprocitySemiPositive
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem semiPosReg_of_eqOn {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {B : LB X}
    {φ ψ : Weight p σ B} {D : ℕ} (h : φ.SemiPosReg D)
    (e : ∀ i, ∀ y ∈ ptsIn p σ (B.U i), ψ.φ i y = φ.φ i y) : ψ.SemiPosReg D := by
  intro i c y hy ξ
  have ho := ChartGlue.isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (B.U i))
  have hm := ChartGlue.mem_over c.e hy.1 hy.2
  have ee : (fun v => (ψ.φ i (c.e.symm v) : ℂ)) =ᶠ[𝓝 (c.e y)] (fun v => (φ.φ i (c.e.symm v) : ℂ)) :=
    Filter.eventually_of_mem (ho.mem_nhds hm) fun v hv => by simp only [e i _ hv.2]
  rw [ReciprocityTheory.L2DbarEstimates.leviV_congr ee]
  exact h i c y hy ξ

theorem exists_addFn_semiPosReg {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
    (M : MLine p σ) (D : ℕ) (hg : ∃ (n : ℕ) (u : Fin n → M.B.Sec), ⨆ i, nonzeroLocus (u i) = ⊤) :
    ∃ (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y), (M.addFn u hu).φ.SemiPosReg D := by
  obtain ⟨ψ, hψ, hψp⟩ := GlobalTheory.T.exists_smooth_semipositive_weight_of_generated k X p σ M.B M.φ.isLB hg
  obtain ⟨u, hu, he⟩ := GlobalTheory.T.smooth_weights_differ_by_smooth_function k X p σ M.B M.φ ψ M.cInf hψ
  exact ⟨u, hu, semiPosReg_of_eqOn (hψp D) fun i y hy => (he i y hy).symm⟩

end GlobalTheory.Mix

theorem GlobalTheory.Mix.side_eq_of_generated : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (M N : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t), (∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → (∀ i, (L i).φ.SemiPosReg (e + 1)) → (∃ (n : ℕ) (u : Fin n → M.B.Sec), ⨆ i, nonzeroLocus (u i) = ⊤) → (∃ (n : ℕ) (u : Fin n → N.B.Sec), ⨆ i, nonzeroLocus (u i) = ⊤) → side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) = side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht) := by
  intro hP F _ X _ _ p σ e hproj hdim L M N s hs t ht hz hL hgM hgN
  obtain ⟨u, hu, hMu⟩ := GlobalTheory.Mix.exists_addFn_semiPosReg M (e + 1) hgM
  obtain ⟨v, hv, hNv⟩ := GlobalTheory.Mix.exists_addFn_semiPosReg N (e + 1) hgN
  have hz' : ∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus t ∨ z ∈ nonzeroLocus s := fun z h => (hz z h).symm
  have h1 := GlobalTheory.T.reciprocityDefect_independent_firstMetric hP F X p σ e hproj hdim L M N s hs t ht hz u hu
  have h2 := GlobalTheory.T.reciprocityDefect_independent_firstMetric hP F X p σ e hproj hdim L N (M.addFn u hu) t ht s hs hz' v hv
  have h3 := GlobalTheory.T.reciprocityFormula_le_semipositive hP F X p σ e hproj hdim L (M.addFn u hu) (N.addFn v hv) s hs t ht hz hL hNv
  have h4 := GlobalTheory.T.reciprocityFormula_le_semipositive hP F X p σ e hproj hdim L (N.addFn v hv) (M.addFn u hu) t ht s hs hz' hL hMu
  have d1 : divOfSec (M.addFn u hu).φ.isLB s hs = divOfSec M.φ.isLB s hs := rfl
  have d2 : divOfSec (N.addFn v hv).φ.isLB t ht = divOfSec N.φ.isLB t ht := rfl
  rw [d1, d2] at h3 h4
  rw [d1] at h2
  linarith
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFramePointStalkCompatStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_frame_point_stalk_compat : Hypotheses2 → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y _ _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (y : Y₀ TF.X Z) (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V), IsLocalHom g → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → evI y' (GlobalTheory.FlatLine.idem Z) ≠ 0 → ∀ w : AllWt.Psi p.T.Q.H → ℤ, ∃ t : GlobalTheory.FlatTw.TwSec Y.U (xiR (Fm.D x ι)) Z (AllWt.wtOf (dat p i) (GlobalTheory.FlatLine.parWt (dat p i) w) 0), vV T.V (evI y' t.sig) = 0 := by
  first | exact @GlobalTheory.FlatValZero.flat_val_zero | exact GlobalTheory.FlatValZero.flat_val_zero | (intros; apply GlobalTheory.FlatValZero.flat_val_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteIffTateModuleMapInjectiveAndIsogenyIffStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFinite_iff_tateModuleMap_injective_and_isogeny_iff : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (A B : AbVar K) (f : A ⟶ B), (IsFinite f.hom.left ↔ Function.Injective (tmap l A B f)) ∧ (IsIsogeny f ↔ Function.Bijective (vmap l f)) := by
  first | exact @GlobalTheory.AV.AbVar.isFinite_iff_tmap_injective_and_isIsogeny_iff_vmap_bijective | exact GlobalTheory.AV.AbVar.isFinite_iff_tmap_injective_and_isIsogeny_iff_vmap_bijective | (intros; apply GlobalTheory.AV.AbVar.isFinite_iff_tmap_injective_and_isIsogeny_iff_vmap_bijective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMapOfNatMultipleFormalGroupLawStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMapOf_natMultiple_formalGroupLaw : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Katz.Chart G d) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), c.IsLawOf μ → ∀ j : ℕ, c.IsMapOf c ((j : ℤ_[p]) • 𝟙 G) (nmul μ j) := by
  first | exact @GlobalTheory.Katz.Chart.isMapOf_nmul | exact GlobalTheory.Katz.Chart.isMapOf_nmul | (intros; apply GlobalTheory.Katz.Chart.isMapOf_nmul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfIrreducibleProperSpecialFibreCompleteDStatement
section
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_of_irreducible_properSpecialFibre_completeDvr : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of O)), IrreducibleSpace X → IsSeparated f → LocallyOfFiniteType f → QuasiCompact f → (∃ x : X, f x = IsLocalRing.closedPoint O) → IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))) → IsProper f := by
  first | exact @GlobalTheory.FibreProper.isProper_of_irreducible_of_isProper_specialFibre | exact GlobalTheory.FibreProper.isProper_of_irreducible_of_isProper_specialFibre | (intros; apply GlobalTheory.FibreProper.isProper_of_irreducible_of_isProper_specialFibre <;> assumption)
end


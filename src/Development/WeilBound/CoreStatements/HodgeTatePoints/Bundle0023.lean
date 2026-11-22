import Development.WeilBound.CoreStatements.HodgeTatePoints.TwpdivHopf
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0005
import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0021
import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfSec

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.GiResAlg
section
open GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace PositivityTheory.HtPt.Gi

variable {R : Type} [CommRing R] {T T' : Type} [CommGroup T] [CommGroup T']

theorem pow_pull [Finite T] {B : Subalgebra R (T → R)} (hB : IsHopfOrder B) {f : T → R} (hf : f ∈ B) (k : ℕ) :
    (fun t => f (t ^ k)) ∈ B := by
  induction k generalizing f with
  | zero =>
    have e : (fun t : T => f (t ^ 0)) = algebraMap R (T → R) (f 1) := by
      funext t
      simp
    rw [e]
    exact B.algebraMap_mem _
  | succ k ih =>
    let L : (T × T → R) →ₗ[R] (T → R) :=
      { toFun := fun g t => g (t ^ k, t)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hmem : ∀ g ∈ prodSpan B, L g ∈ B := by
      intro g hg
      induction hg using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, ha, b, hb, rfl⟩ := hx
        exact B.mul_mem (ih ha) hb
      | zero =>
        rw [map_zero]
        exact B.zero_mem
      | add x y _ _ hx hy =>
        rw [map_add]
        exact B.add_mem hx hy
      | smul r x _ hx =>
        rw [map_smul]
        exact B.smul_mem hx r
    have e : (fun t : T => f (t ^ (k + 1))) = L (fun z : T × T => f (z.1 * z.2)) := by
      funext t
      simp [L, pow_succ]
    rw [e]
    exact hmem _ (hB.comul f hf)

def IsLoc (H : Subgroup T) (B : Subalgebra R (T → R)) : Prop :=
  ∀ f : T → R, (∀ t, ∃ b ∈ B, ∀ h ∈ H, b h = f (t * h)) → f ∈ B

theorem isLoc_of_ind {H : Subgroup T} {B : Subalgebra R (T → R)}
    (h : B = indOrder H.subtype (resOrder H.subtype B)) : IsLoc H B := by
  intro f hf
  rw [h]
  change ∀ t : T, (fun x : H => f (t * H.subtype x)) ∈ resOrder H.subtype B
  intro t
  obtain ⟨b, hb, hbf⟩ := hf t
  refine Subalgebra.mem_map.2 ⟨b, hb, ?_⟩
  funext x
  simp [GlobalTheory.CompanionTheory.Ar.BT.pullFun, hbf x x.2]

open Classical in

def cosetInd (R : Type) [CommRing R] (H : Subgroup T) (c : T ⧸ H) : T → R :=
  fun t => if (t : T ⧸ H) = c then 1 else 0

theorem cosetInd_mul (H : Subgroup T) (c : T ⧸ H) (t : T) {h : T} (hh : h ∈ H) :
    cosetInd R H c (t * h) = cosetInd R H c t := by
  have e : ((t * h : T) : T ⧸ H) = (t : T ⧸ H) := QuotientGroup.mk_mul_of_mem t hh
  unfold cosetInd
  rw [e]

theorem cosetInd_mem {H : Subgroup T} {B : Subalgebra R (T → R)} (hl : IsLoc H B) (c : T ⧸ H) :
    cosetInd R H c ∈ B := by
  apply hl
  intro t
  refine ⟨algebraMap R (T → R) (cosetInd R H c t), B.algebraMap_mem _, fun h hh => ?_⟩
  simp [cosetInd_mul H c t hh]

theorem sum_cosetInd (H : Subgroup T) [Fintype (T ⧸ H)] (F : T ⧸ H → T → R) (t : T) :
    (∑ c, cosetInd R H c * F c) t = F t t := by
  simp [cosetInd, Finset.sum_apply]

variable [Finite T'] {H : Subgroup T} {H' : Subgroup T'} {B : Subalgebra R (T → R)} {B' : Subalgebra R (T' → R)}
  (ι : T →* T')

private theorem translate_mem_of_isHopfOrder' {U : Type} [CommGroup U] {A : Subalgebra R (U → R)} (hA : IsHopfOrder A)
    {f : U → R} (hf : f ∈ A) (u : U) : (fun x => f (u * x)) ∈ A := by
  let L : (U × U → R) →ₗ[R] (U → R) :=
    { toFun := fun g x => g (u, x)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hmem : ∀ g ∈ prodSpan A, L g ∈ A := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      convert A.smul_mem hb (a u) using 1
      funext x
      simp [L]
    | zero =>
      rw [map_zero]
      exact A.zero_mem
    | add x y _ _ hx hy =>
      rw [map_add]
      exact A.add_mem hx hy
    | smul r x _ hx =>
      rw [map_smul]
      exact A.smul_mem hx r
  exact hmem _ (hA.comul f hf)

theorem res_iff_abs (hB : IsHopfOrder B) (hB' : IsHopfOrder B') (hl : IsLoc H B) (hl' : IsLoc H' B')
    (hH : ∀ t, ι t ∈ H' → t ∈ H)
    (ha : ∀ f ∈ B', ∃ g ∈ B, ∀ h ∈ H, g h = f (ι h)) (hb : ∀ g ∈ B, ∃ f ∈ B', ∀ h ∈ H, g h = f (ι h))
    (g : T → R) : g ∈ B ↔ ∃ f ∈ B', ∀ t, g t = f (ι t) := by
  classical
  constructor
  · intro hg
    haveI : Fintype (T' ⧸ H') := Fintype.ofFinite _
    have hex : ∀ t : T, ∃ f ∈ B', ∀ h ∈ H, g (t * h) = f (ι h) :=
      fun t => hb _ (translate_mem_of_isHopfOrder' hB hg t)
    choose fr hfr hfrH using hex
    let rep : T' ⧸ H' → T := fun c =>
      if hc : ∃ t : T, (ι t : T' ⧸ H') = c then hc.choose else 1
    have hrep : ∀ t0 : T, ((ι (rep (ι t0 : T' ⧸ H')) : T') : T' ⧸ H') = (ι t0 : T' ⧸ H') := by
      intro t0
      have hc : ∃ t : T, (ι t : T' ⧸ H') = (ι t0 : T' ⧸ H') := ⟨t0, rfl⟩
      simp only [rep, dif_pos hc]
      exact hc.choose_spec
    let F : T' ⧸ H' → T' → R := fun c s => fr (rep c) ((ι (rep c))⁻¹ * s)
    refine ⟨∑ c, cosetInd R H' c * F c, ?_, ?_⟩
    · refine Subalgebra.sum_mem _ (fun c _ => Subalgebra.mul_mem _ (cosetInd_mem hl' c) ?_)
      exact translate_mem_of_isHopfOrder' hB' (hfr (rep c)) _
    · intro t0
      rw [sum_cosetInd]
      set r := rep (ι t0 : T' ⧸ H') with hr
      have hmem' : (ι r)⁻¹ * ι t0 ∈ H' := QuotientGroup.eq.mp (hrep t0)
      have hmem : r⁻¹ * t0 ∈ H := hH _ (by simpa [map_mul, map_inv] using hmem')
      have := hfrH r _ hmem
      simp only [mul_inv_cancel_left] at this
      simp only [F, ← hr]
      rw [this, map_mul, map_inv]
  · rintro ⟨f, hf, hgf⟩
    apply hl
    intro t
    obtain ⟨g', hg', hg'H⟩ := ha _ (translate_mem_of_isHopfOrder' hB' hf (ι t))
    refine ⟨g', hg', fun h hh => ?_⟩
    rw [hg'H h hh, hgf, map_mul]

abbrev torsJ (B' : Subalgebra R (T' → R)) (N : ℕ) : Ideal B' :=
  Ideal.span {g : B' | ∃ h ∈ B', ∀ t, g.1 t = h (t ^ N) - h 1}

private theorem translate_mem_torsJ_of_pow_eq_one {N : ℕ} (hB' : IsHopfOrder B') {v : T'} (hv : v ^ N = 1) (j : B')
    (hj : j ∈ torsJ B' N) :
    (⟨fun x => j.1 (v * x), translate_mem_of_isHopfOrder' hB' j.2 v⟩ : B') ∈ torsJ B' N := by
  let τ : B' →+* B' :=
    { toFun := fun g => ⟨fun x => g.1 (v * x), translate_mem_of_isHopfOrder' hB' g.2 v⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hle : torsJ B' N ≤ Ideal.comap τ (torsJ B' N) := by
    refine Ideal.span_le.2 ?_
    rintro g ⟨h, hh, hg⟩
    rw [SetLike.mem_coe, Ideal.mem_comap]
    apply Ideal.subset_span
    refine ⟨h, hh, fun x => ?_⟩
    show g.1 (v * x) = h (x ^ N) - h 1
    rw [hg, mul_pow, hv, one_mul]
  exact hle hj

theorem ker_abs {N : ℕ} (hB' : IsHopfOrder B') (hl' : IsLoc H' B') (hN : ∀ t, ι t ^ N = 1)
    (hdiv : ∀ s : T', s ^ N ∈ H' → ∃ t, (ι t : T' ⧸ H') = s)
    (hc : ∀ f ∈ B', (∀ t, f (ι t) = 0) → ∃ j ∈ torsJ B' N, ∀ h ∈ H', j.1 h = f h)
    (f : B') (hf : ∀ t, f.1 (ι t) = 0) : f ∈ torsJ B' N := by
  classical
  haveI : Fintype (T' ⧸ H') := Fintype.ofFinite _
  have hE : ∀ c : T' ⧸ H', cosetInd R H' c ∈ B' := fun c => cosetInd_mem hl' c
  have hdecomp : f = ∑ c, (⟨cosetInd R H' c, hE c⟩ : B') * f := by
    apply Subtype.ext
    funext x
    have key := sum_cosetInd (R := R) H' (fun _ => f.1) x
    simp only [Finset.sum_apply, Pi.mul_apply] at key
    simp [Finset.sum_apply, key]
  rw [hdecomp]
  refine Ideal.sum_mem _ (fun c _ => ?_)
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective c
  by_cases hs : s ^ N ∈ H'
  · obtain ⟨t, ht⟩ := hdiv s hs
    have hfu : (fun x => f.1 (ι t * x)) ∈ B' := translate_mem_of_isHopfOrder' hB' f.2 (ι t)
    obtain ⟨j, hj, hjH⟩ := hc _ hfu (fun t' => by
      show f.1 (ι t * ι t') = 0
      rw [← map_mul]
      exact hf _)
    have hv : (ι t)⁻¹ ^ N = 1 := by rw [inv_pow, hN, inv_one]
    have hτ := translate_mem_torsJ_of_pow_eq_one hB' hv j hj
    have heq : (⟨cosetInd R H' (s : T' ⧸ H'), hE _⟩ : B') * f =
        (⟨cosetInd R H' (s : T' ⧸ H'), hE _⟩ : B') *
          ⟨fun x => j.1 ((ι t)⁻¹ * x), translate_mem_of_isHopfOrder' hB' j.2 (ι t)⁻¹⟩ := by
      apply Subtype.ext
      funext x
      show cosetInd R H' (s : T' ⧸ H') x * f.1 x = cosetInd R H' (s : T' ⧸ H') x * j.1 ((ι t)⁻¹ * x)
      by_cases hx : (x : T' ⧸ H') = s
      · have hmem : (ι t)⁻¹ * x ∈ H' := QuotientGroup.eq.mp (ht.trans hx.symm)
        simp only [hjH _ hmem, mul_inv_cancel_left]
      · simp [cosetInd, hx]
    rw [heq]
    exact Ideal.mul_mem_left _ _ hτ
  · let h0 : T' → R := cosetInd R H' ((s : T' ⧸ H') ^ N)
    have hG : (fun x => h0 (x ^ N) - h0 1) ∈ B' := by
      have h1 := pow_pull hB' (hE ((s : T' ⧸ H') ^ N)) N
      exact Subalgebra.sub_mem _ h1 (B'.algebraMap_mem (h0 1))
    let G : B' := ⟨fun x => h0 (x ^ N) - h0 1, hG⟩
    have hGJ : G ∈ torsJ B' N := Ideal.subset_span ⟨h0, hE _, fun x => rfl⟩
    have heq : (⟨cosetInd R H' (s : T' ⧸ H'), hE _⟩ : B') * f =
        ((⟨cosetInd R H' (s : T' ⧸ H'), hE _⟩ : B') * f) * G := by
      apply Subtype.ext
      funext x
      show cosetInd R H' (s : T' ⧸ H') x * f.1 x =
        cosetInd R H' (s : T' ⧸ H') x * f.1 x * (h0 (x ^ N) - h0 1)
      by_cases hx : (x : T' ⧸ H') = s
      · have e1 : h0 (x ^ N) = 1 := by
          simp [h0, cosetInd, QuotientGroup.mk_pow, hx]
        have e2 : h0 1 = 0 := by
          simp only [h0, cosetInd]
          rw [if_neg]
          intro h1
          apply hs
          rw [← QuotientGroup.mk_pow] at h1
          have := QuotientGroup.eq.mp h1
          simpa using this
        rw [e1, e2, sub_zero, mul_one]
      · simp [cosetInd, hx]
    rw [heq]
    exact Ideal.mul_mem_left _ _ hGJ

end PositivityTheory.HtPt.Gi
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHopfReg
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

noncomputable section

namespace PositivityTheory.HtPt.Htat.StalkDivisibility

def constSec {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) (d : R) : Γ(X, U) :=
  (p.appLE ⊤ U (fun _ _ => trivial)).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom d)

section valAt

variable {B C R : Type} [CommRing B] [CommRing C] [CommRing R] {X Y : Scheme.{0}}

theorem valAt_congr {x y : Spec (CommRingCat.of B) ⟶ X} (e : x = y) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (h' : ⊤ ≤ y ⁻¹ᵁ U) (s : Γ(X, U)) : valAt x U h s = valAt y U h' s := by
  subst e; rfl

theorem valAt_res (x : Spec (CommRingCat.of B) ⟶ X) {U V : X.Opens} (i : V ⟶ U) (hV : ⊤ ≤ x ⁻¹ᵁ V)
    (hU : ⊤ ≤ x ⁻¹ᵁ U) (s : Γ(X, U)) :
    valAt x V hV ((X.presheaf.map i.op).hom s) = valAt x U hU s :=
  congrArg (fun φ => (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom (φ.hom s)) (x.map_appLE hV i.op)

theorem valAt_mul (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a b : Γ(X, U)) :
    valAt x U h (a * b) = valAt x U h a * valAt x U h b := by
  simp [valAt]

theorem valAt_sub (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a b : Γ(X, U)) :
    valAt x U h (a - b) = valAt x U h a - valAt x U h b := by
  simp [valAt]

theorem valAt_comp (x : Spec (CommRingCat.of B) ⟶ Y) (F : Y ⟶ X) (U : X.Opens) (h : ⊤ ≤ (x ≫ F) ⁻¹ᵁ U)
    (s : Γ(X, U)) : valAt (x ≫ F) U h s = valAt x (F ⁻¹ᵁ U) h ((F.app U).hom s) := by
  simp only [valAt, Scheme.Hom.comp_appLE]
  rfl

theorem specMap_appLE_top (φ : B →+* C) (e) (r : Γ(Spec (CommRingCat.of B), ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom (((Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ e).hom r) =
      φ ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom r) := by
  have h : (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ e = (Spec.map (CommRingCat.ofHom φ)).appTop := by
    exact (Scheme.Hom.app_eq_appLE _).symm
  rw [h]
  exact congrArg (fun ψ => ψ.hom r) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))

theorem valAt_spec (κ : B →+* C) (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (h' : ⊤ ≤ (Spec.map (CommRingCat.ofHom κ) ≫ x) ⁻¹ᵁ U) (s : Γ(X, U)) :
    valAt (Spec.map (CommRingCat.ofHom κ) ≫ x) U h' s = κ (valAt x U h s) := by
  have e := Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom κ)) x U ⊤ ⊤ h (fun _ _ => trivial)
  simp only [valAt]
  rw [← e]
  exact specMap_appLE_top κ _ _

theorem valAt_const (p : X ⟶ Spec (CommRingCat.of R)) (x : Spec (CommRingCat.of B) ⟶ X) (φ : R →+* B)
    (hx : x ≫ p = Spec.map (CommRingCat.ofHom φ)) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (d : R) :
    valAt x U h (constSec p U d) = φ d := by
  have e := Scheme.Hom.appLE_comp_appLE x p ⊤ U ⊤ (fun _ _ => trivial) h
  have key : ∀ (y : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R)) (_ : y = Spec.map (CommRingCat.ofHom φ)) (e' : ⊤ ≤ y ⁻¹ᵁ ⊤),
      (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((y.appLE ⊤ ⊤ e').hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom d)) = φ d := by
    intro y hy e'
    subst hy
    rw [specMap_appLE_top]
    simp
  change (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom
    ((p.appLE ⊤ U (fun _ _ => trivial) ≫ x.appLE U ⊤ h).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom d)) = φ d
  rw [e]
  exact key _ hx _

theorem constSec_res (p : X ⟶ Spec (CommRingCat.of R)) {U V : X.Opens} (i : V ⟶ U) (d : R) :
    (X.presheaf.map i.op).hom (constSec p U d) = constSec p V d :=
  congrArg (fun ψ => ψ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom d))
    (p.appLE_map (U := ⊤) (V := U) (V' := V) (fun _ _ => trivial) i.op)

theorem app_constSec {R' : Type} [CommRing R'] (p : X ⟶ Spec (CommRingCat.of R)) (p' : Y ⟶ Spec (CommRingCat.of R'))
    (F : Y ⟶ X) (φ : R →+* R') (hF : F ≫ p = p' ≫ Spec.map (CommRingCat.ofHom φ)) (U : X.Opens) (d : R) :
    (F.app U).hom (constSec p U d) = constSec p' (F ⁻¹ᵁ U) (φ d) := by
  have e₁ := Scheme.Hom.appLE_comp_appLE F p ⊤ U (F ⁻¹ᵁ U) (fun _ _ => trivial) le_rfl
  have e₂ : ∀ (y : Y ⟶ Spec (CommRingCat.of R)) (_ : y = p' ≫ Spec.map (CommRingCat.ofHom φ)) (e' : F ⁻¹ᵁ U ≤ y ⁻¹ᵁ ⊤),
      (y.appLE ⊤ (F ⁻¹ᵁ U) e').hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom d) = constSec p' (F ⁻¹ᵁ U) (φ d) := by
    intro y hy e'
    subst hy
    rw [Scheme.Hom.comp_appLE]
    have n := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)
    have n' := congrArg (fun ψ => ψ.hom d) n
    simp only [constSec]
    change (p'.appLE _ _ _).hom (((Spec.map (CommRingCat.ofHom φ)).appTop).hom _) = _
    exact congrArg (p'.appLE ⊤ (F ⁻¹ᵁ U) (fun _ _ => trivial)).hom n'.symm
  rw [← e₂ _ hF (fun _ _ => trivial), ← e₁, Scheme.Hom.app_eq_appLE]
  rfl

theorem dvd_of_stalkMap_dvd (r : Y ⟶ X) [Flat r] (z : Y) {a b : X.presheaf.stalk (r z)}
    (h : (r.stalkMap z).hom a ∣ (r.stalkMap z).hom b) : a ∣ b := by
  let _ := (r.stalkMap z).hom.toAlgebra
  have : Module.Flat (X.presheaf.stalk (r z)) (Y.presheaf.stalk z) := Flat.stalkMap r z
  have : IsLocalHom (algebraMap (X.presheaf.stalk (r z)) (Y.presheaf.stalk z)) :=
    inferInstanceAs (IsLocalHom (r.stalkMap z).hom)
  have : Module.FaithfullyFlat (X.presheaf.stalk (r z)) (Y.presheaf.stalk z) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  rw [← Ideal.mem_span_singleton, ← Ideal.comap_map_eq_self_of_faithfullyFlat (B := Y.presheaf.stalk z) (Ideal.span {a}),
    Ideal.mem_comap, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
  exact h

theorem top_le_of_spec_comp {K L : Type} [Field K] [Field L] (κ : K →+* L) (x : Spec (CommRingCat.of K) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ (Spec.map (CommRingCat.ofHom κ) ≫ x) ⁻¹ᵁ U) : ⊤ ≤ x ⁻¹ᵁ U := by
  intro y _
  have : Subsingleton (Spec (CommRingCat.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have : Nonempty (Spec (CommRingCat.of L)) := inferInstanceAs (Nonempty (PrimeSpectrum L))
  obtain ⟨w⟩ := this
  have hw := h (show w ∈ (⊤ : (Spec (CommRingCat.of L)).Opens) from trivial)
  rw [Subsingleton.elim y (Spec.map (CommRingCat.ofHom κ) w)]
  simpa using hw

end valAt

theorem regularAt_of_baseChange : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → Module.Flat R R' → ∀ κ : FractionRing R →+* FractionRing R', κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R') → ∀ (f : T → FractionRing R) (g' : Γ'.G.left), Γ'.RegularAt (fun t => κ (f t)) g' → Γ.RegularAt f (F g') := by
  intro R _ _ T _ _ Γ R' _ _ _ Γ' F hbc hfl κ hκ f g' hreg
  obtain ⟨U', hgU', s', hs'⟩ := hreg
  obtain ⟨d, hd0, U, hgU, s, hs⟩ := GlobalTheory.T.exists_denominator_regular R T Γ f (F g')
  have hφ : Flat (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr hfl)
  have hF : Flat F := MorphismProperty.of_isPullback (P := @Flat) hbc.cart.flip hφ
  have hsq : F ≫ Γ.G.hom = Γ'.G.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) := hbc.cart.w
  let W' : Γ'.G.left.Opens := (F ⁻¹ᵁ U) ⊓ U'
  have hgW' : g' ∈ W' := ⟨hgU, hgU'⟩
  let i₁ : W' ⟶ F ⁻¹ᵁ U := homOfLE inf_le_left
  let i₂ : W' ⟶ U' := homOfLE inf_le_right
  have key : (Γ'.G.left.presheaf.map i₁.op).hom ((F.app U).hom s) =
      constSec Γ'.G.hom W' (algebraMap R R' d) * (Γ'.G.left.presheaf.map i₂.op).hom s' := by
    refine sub_eq_zero.mp (PositivityTheory.HtPt.Twhopf.sec_inj R' T Γ' W' _ fun t h => ?_)
    have h₁ : ⊤ ≤ (Γ'.pt t).left ⁻¹ᵁ (F ⁻¹ᵁ U) := fun x hx => (h hx).1
    have h₂ : ⊤ ≤ (Γ'.pt t).left ⁻¹ᵁ U' := fun x hx => (h hx).2
    have hpt := GlobalTheory.T.base_change_points_compat R T Γ R' Γ' F hbc κ hκ t
    have h₃ : ⊤ ≤ (Spec.map (CommRingCat.ofHom κ) ≫ (Γ.pt t).left) ⁻¹ᵁ U := by
      rw [← hpt]; exact h₁
    have h₄ : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U := top_le_of_spec_comp κ _ U h₃
    have hw' : (Γ'.pt t).left ≫ Γ'.G.hom =
        Spec.map (CommRingCat.ofHom (algebraMap R' (FractionRing R'))) := Over.w (Γ'.pt t)
    rw [valAt_sub, valAt_mul, valAt_res _ i₁ h h₁, valAt_res _ i₂ h h₂, hs' t h₂,
      valAt_const _ _ (algebraMap R' (FractionRing R')) hw', ← valAt_comp _ F U h₁,
      valAt_congr hpt U h₁ h₃, valAt_spec κ _ U h₄ h₃, hs t h₄, map_mul]
    have : κ (algebraMap R _ d) = algebraMap R' _ (algebraMap R R' d) := congrArg (fun ψ => ψ d) hκ
    rw [this, sub_self]
  have hdvd : Γ.G.left.presheaf.germ U (F g') hgU (constSec Γ.G.hom U d) ∣
      Γ.G.left.presheaf.germ U (F g') hgU s := by
    apply dvd_of_stalkMap_dvd F g'
    refine ⟨Γ'.G.left.presheaf.germ W' g' hgW' ((Γ'.G.left.presheaf.map i₂.op).hom s'), ?_⟩
    have e₁ := Scheme.Hom.germ_stalkMap_apply F U g' hgU s
    have e₂ := Scheme.Hom.germ_stalkMap_apply F U g' hgU (constSec Γ.G.hom U d)
    rw [app_constSec _ _ F _ hsq] at e₂
    have e₃ := Γ'.G.left.presheaf.germ_res_apply i₁ g' hgW' ((F.app U).hom s)
    have e₄ := Γ'.G.left.presheaf.germ_res_apply i₁ g' hgW' (constSec Γ'.G.hom (F ⁻¹ᵁ U) (algebraMap R R' d))
    rw [constSec_res] at e₄
    rw [key, map_mul] at e₃
    exact e₁.trans (e₃.symm.trans (by rw [e₄, ← e₂]))
  obtain ⟨x, hx⟩ := hdvd
  obtain ⟨W, hgW, s₀, rfl⟩ := Γ.G.left.presheaf.exists_germ_eq x
  let P : Γ.G.left.Opens := U ⊓ W
  have hgP : F g' ∈ P := ⟨hgU, hgW⟩
  let j₁ : P ⟶ U := homOfLE inf_le_left
  let j₂ : P ⟶ W := homOfLE inf_le_right
  have hP : Γ.G.left.presheaf.germ U (F g') hgU s = Γ.G.left.presheaf.germ P (F g') hgP
      (constSec Γ.G.hom P d * (Γ.G.left.presheaf.map j₂.op).hom s₀) := by
    rw [hx, map_mul, TopCat.Presheaf.germ_res_apply, ← constSec_res _ j₁, TopCat.Presheaf.germ_res_apply]
  obtain ⟨V, hV, iU, iP, hres⟩ := TopCat.Presheaf.germ_eq _ _ hgU hgP _ _ hP
  refine ⟨V, hV, (Γ.G.left.presheaf.map (iP ≫ j₂).op).hom s₀, fun t h => ?_⟩
  have hU : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U := fun x hx => iU.le (h hx)
  have hPt : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ P := fun x hx => iP.le (h hx)
  have hWt : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ W := fun x hx => (iP ≫ j₂).le (h hx)
  have hw : (Γ.pt t).left ≫ Γ.G.hom =
      Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) := Over.w (Γ.pt t)
  have hK : algebraMap R (FractionRing R) d ≠ 0 := by
    simpa using hd0
  refine mul_left_cancel₀ hK ?_
  have e₁ := congrArg (valAt (Γ.pt t).left V h) hres
  rw [valAt_res _ iU h hU, hs t hU, valAt_res _ iP h hPt, valAt_mul, valAt_const _ _ _ hw,
    valAt_res _ j₂ hPt hWt] at e₁
  rw [valAt_res _ (iP ≫ j₂) h hWt]
  exact e₁.symm

end PositivityTheory.HtPt.Htat.StalkDivisibility

theorem PositivityTheory.HtPt.Htat.bt_reg_descent : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → Module.Flat R R' → ∀ κ : FractionRing R →+* FractionRing R', κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R') → ∀ (f : T → FractionRing R) (g' : Γ'.G.left), Γ'.RegularAt (fun t => κ (f t)) g' → Γ.RegularAt f (F g') :=
  @PositivityTheory.HtPt.Htat.StalkDivisibility.regularAt_of_baseChange
end
end


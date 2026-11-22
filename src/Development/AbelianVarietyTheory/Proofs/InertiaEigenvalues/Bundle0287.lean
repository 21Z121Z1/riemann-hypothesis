import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleStd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCoboundariesAmongBlockCocyclesLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0269
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeOfFrobeniusEquationCyclotomicFixed
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0270
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KernelInverseFibreProductLattices
section
noncomputable section

namespace GlobalTheory.RedFun.SubLat

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open GlobalTheory.TopSteps.StdAdm
open scoped LaurentSeries PowerSeries TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL] [Algebra Qp LL]
  [CommRing O] [Algebra O LL] [TopologicalSpace LL]

def subLattice [IsDomain O] [IsPrincipalIdealRing O] (T : LocLat G Qp LL O) {lam : O}
    (hl : algebraMap O LL lam ≠ 0) (P : Submodule O ↥T.L.T) (hg : ∀ g, ∀ x ∈ P, latRep T.L g x ∈ P)
    (hP : ∀ x, lam • x ∈ P) : Lattice (O := O) T.ρ where
  T := P.map T.L.T.subtype
  stable := by
    rintro g _ ⟨x, hx, rfl⟩
    exact ⟨latRep T.L g x, hg g x hx, rfl⟩
  fg := by
    have := finite_lat T
    exact (IsNoetherian.noetherian _).map _
  free := by
    have := finite_lat T
    have := T.L.free
    have : Module.Free O ↥P := Module.free_of_finite_type_torsion_free'
    exact Module.Free.of_equiv (Submodule.equivMapOfInjective _ T.L.T.injective_subtype _)
  span := by
    rw [eq_top_iff, ← T.L.span, Submodule.span_le]
    intro y hy
    have h1 : lam • y ∈ P.map T.L.T.subtype := ⟨lam • ⟨y, hy⟩, hP _, rfl⟩
    have h2 := Submodule.smul_mem _ (algebraMap O LL lam)⁻¹ (Submodule.subset_span (R := LL) h1)
    rwa [← algebraMap_smul LL lam y, inv_smul_smul₀ hl] at h2

variable {k : Type} [Field k] [Algebra O k]

omit [Algebra O LL] in

theorem lam_smul {lam : O} (hk : algebraMap O k lam = 0) {m : ℕ} (t : Fin m → k) : lam • t = 0 := by
  ext i
  simp [Algebra.smul_def, hk]

theorem exists_ker [IsDomain O] [IsPrincipalIdealRing O] {lam : O} (hl : algebraMap O LL lam ≠ 0)
    (hk : algebraMap O k lam = 0) (T : LocLat G Qp LL O) (A : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k))
    (hq : Onto T A q) : ∃ (T' : LocLat G Qp LL O) (f : LatHom T'.L T.L),
      ∀ x : ↥T.L.T, q x = 0 ↔ ∃ y ∈ T'.L.T, f.f y = x := by
  have hq2 : ∀ σ x, q (latRep T.L σ x) = A.ρ σ (q x) := hq.2
  have hP : ∀ x, lam • x ∈ LinearMap.ker q := fun x => by
    rw [LinearMap.mem_ker, map_smul, lam_smul hk]
  have hg : ∀ σ, ∀ x ∈ LinearMap.ker q, latRep T.L σ x ∈ LinearMap.ker q := fun σ x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [hq2, hx, map_zero]
  refine ⟨{ T with L := subLattice T hl (LinearMap.ker q) hg hP },
    ⟨LinearMap.id, fun _ _ => rfl, continuous_id, ?_⟩, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · intro x
    constructor
    · intro hx
      exact ⟨x, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨z, hz, rfl⟩, h⟩
      have hzx : z = x := Subtype.ext h
      subst hzx
      exact hz

theorem exists_inv {lam : O} (hl : algebraMap O LL lam ≠ 0) (T T' : LocLat G Qp LL O) (f : LatHom T'.L T.L)
    (hf : Function.Injective f.f) (h : ∀ x ∈ T.L.T, ∃ y ∈ T'.L.T, f.f y = lam • x) :
    ∃ h : LatHom T.L T'.L, ∀ x, f.f (h.f x) = algebraMap O LL lam • x := by
  have hsurj : Function.Surjective f.f := by
    have hle : Submodule.span LL (T.L.T : Set T.V) ≤ LinearMap.range f.f := by
      rw [Submodule.span_le]
      intro x hx
      obtain ⟨y, -, hy⟩ := h x hx
      refine ⟨(algebraMap O LL lam)⁻¹ • y, ?_⟩
      rw [map_smul, hy, ← algebraMap_smul LL lam x, inv_smul_smul₀ hl]
    rw [T.L.span] at hle
    exact fun x => hle Submodule.mem_top
  let e := LinearEquiv.ofBijective f.f ⟨hf, hsurj⟩
  have h1 : ∀ z, f.f (e.symm z) = z := fun z => e.apply_symm_apply z
  let c := algebraMap O LL lam
  refine ⟨⟨c • (e.symm : T.V →ₗ[LL] T'.V), ?_, IsModuleTopology.continuous_of_linearMap _, ?_⟩, ?_⟩
  · intro σ x
    apply hf
    simp only [LinearMap.smul_apply, LinearEquiv.coe_coe, map_smul, f.equiv, h1]
  · intro x hx
    obtain ⟨y, hy, hfy⟩ := h x hx
    have hxy : (c • (e.symm : T.V →ₗ[LL] T'.V)) x = y := by
      apply hf
      rw [LinearMap.smul_apply, map_smul, LinearEquiv.coe_coe, h1, hfy, algebraMap_smul]
    rw [hxy]
    exact hy
  · intro x
    show f.f ((c • (e.symm : T.V →ₗ[LL] T'.V)) x) = c • x
    rw [LinearMap.smul_apply, map_smul, LinearEquiv.coe_coe, h1]

theorem exists_fibre [IsDomain O] [IsPrincipalIdealRing O] {lam : O} (hl : algebraMap O LL lam ≠ 0)
    (hk : algebraMap O k lam = 0) (T : LocLat G Qp LL O) (A : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k))
    (T' : LocLat G Qp LL O) (A' : Ob k G) (q' : ↥T'.L.T →ₗ[O] (Fin A'.m → k))
    (g : (Fin A.m → k) →ₗ[k] (Fin A'.m → k)) (hq : Onto T A q) (hq' : Onto T' A' q') (hg : IsHom A A' g) :
    ∃ (T'' : LocLat G Qp LL O) (f : LatHom T''.L T.L) (f' : LatHom T''.L T'.L),
      (∀ x ∈ T.L.T, ∃ z ∈ T''.L.T, f.f z = x) ∧
      ∀ z : ↥T''.L.T, q' (GlobalTheory.EtaleExact.latMap f' z) = g (q (GlobalTheory.EtaleExact.latMap f z)) := by
  have hq2 : ∀ σ x, q (latRep T.L σ x) = A.ρ σ (q x) := hq.2
  have hq2' : ∀ σ x, q' (latRep T'.L σ x) = A'.ρ σ (q' x) := hq'.2
  have hg0 : ∀ σ x, g (A.ρ σ x) = A'.ρ σ (g x) := hg
  let φ : ↥(prodLat T T').L.T →ₗ[O] (Fin A'.m → k) :=
    q' ∘ₗ (LinearMap.snd O _ _ ∘ₗ (prodLatEquiv T T').toLinearMap) -
      (g.restrictScalars O) ∘ₗ q ∘ₗ (LinearMap.fst O _ _ ∘ₗ (prodLatEquiv T T').toLinearMap)
  have hφ : ∀ z, φ z = q' (prodLatEquiv T T' z).2 - g (q (prodLatEquiv T T' z).1) := fun z => rfl
  have hP : ∀ z, lam • z ∈ LinearMap.ker φ := fun z => by
    rw [LinearMap.mem_ker, map_smul, lam_smul hk]
  have hst : ∀ σ, ∀ z ∈ LinearMap.ker φ, latRep (prodLat T T').L σ z ∈ LinearMap.ker φ := by
    intro σ z hz
    rw [LinearMap.mem_ker, hφ] at hz ⊢
    simp only [prodLatEquiv_act]
    rw [hq2, hq2', hg0, ← map_sub, hz, map_zero]
  refine ⟨{ prodLat T T' with L := subLattice (prodLat T T') hl (LinearMap.ker φ) hst hP },
    ⟨LinearMap.fst LL T.V T'.V, fun _ _ => rfl, continuous_fst, ?_⟩,
    ⟨LinearMap.snd LL T.V T'.V, fun _ _ => rfl, continuous_snd, ?_⟩, ?_, ?_⟩
  · rintro _ ⟨z, -, rfl⟩
    exact z.2.1
  · rintro _ ⟨z, -, rfl⟩
    exact z.2.2
  · intro x hx
    obtain ⟨x', hx'⟩ := hq'.1 (g (q ⟨x, hx⟩))
    let w : ↥(prodLat T T').L.T := ⟨(x, (x' : T'.V)), hx, x'.2⟩
    refine ⟨(x, (x' : T'.V)), ⟨w, ?_, rfl⟩, rfl⟩
    show φ w = 0
    rw [hφ]
    exact sub_eq_zero.mpr hx'
  · rintro ⟨_, ⟨w, hw, rfl⟩⟩
    have hw' : φ w = 0 := hw
    rw [hφ, sub_eq_zero] at hw'
    exact hw'

theorem ker_inv_fibre : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL] [Algebra Qp LL] [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Algebra O LL] [TopologicalSpace LL] {k : Type} [Field k] [Algebra O k] (lam : O), algebraMap O LL lam ≠ 0 → algebraMap O k lam = 0 → (∀ (T : LocLat G Qp LL O) (A : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)), Onto T A q → ∃ (T' : LocLat G Qp LL O) (f : LatHom T'.L T.L), ∀ x : ↥T.L.T, q x = 0 ↔ ∃ y ∈ T'.L.T, f.f y = x) ∧ (∀ (T T' : LocLat G Qp LL O) (f : LatHom T'.L T.L), Function.Injective f.f → (∀ x ∈ T.L.T, ∃ y ∈ T'.L.T, f.f y = lam • x) → ∃ h : LatHom T.L T'.L, ∀ x, f.f (h.f x) = algebraMap O LL lam • x) ∧ ∀ (T : LocLat G Qp LL O) (A : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)) (T' : LocLat G Qp LL O) (A' : Ob k G) (q' : ↥T'.L.T →ₗ[O] (Fin A'.m → k)) (g : (Fin A.m → k) →ₗ[k] (Fin A'.m → k)), Onto T A q → Onto T' A' q' → IsHom A A' g → ∃ (T'' : LocLat G Qp LL O) (f : LatHom T''.L T.L) (f' : LatHom T''.L T'.L), (∀ x ∈ T.L.T, ∃ z ∈ T''.L.T, f.f z = x) ∧ ∀ z : ↥T''.L.T, q' (GlobalTheory.EtaleExact.latMap f' z) = g (q (GlobalTheory.EtaleExact.latMap f z)) := by
  intro G _ _ Qp LL O _ _ _ _ _ _ _ _ k _ _ lam hl hk
  exact ⟨fun T A q hq => exists_ker hl hk T A q hq, fun T T' f hf h => exists_inv hl T T' f hf h,
    fun T A q T' A' q' g hq hq' hg => exists_fibre hl hk T A q T' A' q' g hq hq' hg⟩

end GlobalTheory.RedFun.SubLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeQuotientsClosedSubQuotSum
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct

noncomputable section

namespace GlobalTheory.RedFun.LatQuot

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL] [Algebra Qp LL]
  [CommRing O] [Algebra O LL] [TopologicalSpace LL] {k : Type} [Field k] [Algebra O k]

def subLattice [IsDomain O] [IsPrincipalIdealRing O] (T : LocLat G Qp LL O) (lam : O)
    (hl : algebraMap O LL lam ≠ 0) (P : Submodule O ↥T.L.T) (hP : ∀ g, ∀ x ∈ P, latRep T.L g x ∈ P)
    (hlam : ∀ x, lam • x ∈ P) : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) T.ρ where
  T := P.map T.L.T.subtype
  stable := by
    rintro g _ ⟨x, hx, rfl⟩
    exact ⟨latRep T.L g x, hP g x hx, rfl⟩
  fg := by
    have := StdAdm.finite_lat T
    exact (IsNoetherian.noetherian _).map _
  free := by
    have := StdAdm.finite_lat T
    have := T.L.free
    have : Module.Free O ↥P := Module.free_of_finite_type_torsion_free'
    exact Module.Free.of_equiv (Submodule.equivMapOfInjective _ T.L.T.injective_subtype _)
  span := by
    rw [eq_top_iff, ← T.L.span, Submodule.span_le]
    intro y hy
    have h1 : lam • y ∈ P.map T.L.T.subtype := ⟨lam • ⟨y, hy⟩, hlam _, rfl⟩
    have h2 := Submodule.smul_mem _ (algebraMap O LL lam)⁻¹ (Submodule.subset_span (R := LL) h1)
    rwa [← algebraMap_smul LL lam y, inv_smul_smul₀ hl] at h2

theorem onto_sub [IsDomain O] [IsPrincipalIdealRing O] (lam : O) (hl : algebraMap O LL lam ≠ 0)
    (hk : algebraMap O k lam = 0) (A B : Ob k G) (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (hf : IsHom A B f)
    (hi : Function.Injective f) (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin B.m → k)) (hq : Onto T B q) :
    ∃ (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)), Onto T A q := by
  obtain ⟨r, hr⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hi)
  have hr' : ∀ x, r (f x) = x := fun x => LinearMap.congr_fun hr x
  let P : Submodule O ↥T.L.T := (LinearMap.range (f.restrictScalars O)).comap q
  have hP : ∀ g, ∀ x ∈ P, latRep T.L g x ∈ P := by
    rintro g x ⟨a, ha⟩
    refine ⟨A.ρ g a, ?_⟩
    have ha' : f a = q x := ha
    change f (A.ρ g a) = q _
    rw [hf, ha', hq.2]
  have hlam : ∀ x, lam • x ∈ P := by
    intro x
    refine ⟨0, ?_⟩
    rw [map_zero, map_smul, ← algebraMap_smul k lam, hk, zero_smul]
  let L := subLattice T lam hl P hP hlam
  have hle : L.T ≤ T.L.T := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  refine ⟨withLat T L, (r.restrictScalars O).comp (q.comp (Submodule.inclusion hle)), ?_, ?_⟩
  · intro a
    obtain ⟨x, hx⟩ := hq.1 (f a)
    refine ⟨⟨x.1, x, ⟨a, hx.symm⟩, rfl⟩, ?_⟩
    change r (q x) = a
    rw [hx, hr']
  · rintro g ⟨_, x, ⟨a, ha⟩, rfl⟩
    have ha' : f a = q x := ha
    change r (q (latRep T.L g x)) = A.ρ g (r (q x))
    rw [hq.2, ← ha', ← hf, hr', hr']

theorem onto_quot (A B : Ob k G) (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (hf : IsHom A B f)
    (hs : Function.Surjective f) (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)) (hq : Onto T A q) :
    Onto T B ((f.restrictScalars O).comp q) := by
  refine ⟨hs.comp hq.1, fun g x => ?_⟩
  change f (q _) = B.ρ g (f (q x))
  rw [hq.2, hf]

theorem onto_sum (A B C : Ob k G) (i : (Fin A.m → k) →ₗ[k] (Fin C.m → k)) (j : (Fin B.m → k) →ₗ[k] (Fin C.m → k))
    (hi : IsHom A C i) (hj : IsHom B C j) (hs : Function.Surjective (i.coprod j))
    (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)) (hq : Onto T A q)
    (T' : LocLat G Qp LL O) (q' : ↥T'.L.T →ₗ[O] (Fin B.m → k)) (hq' : Onto T' B q') :
    Onto (StdAdm.prodLat T T') C (((i.coprod j).restrictScalars O).comp
      ((q.prodMap q').comp (StdAdm.prodLatEquiv T T').toLinearMap)) := by
  refine ⟨hs.comp ((hq.1.prodMap hq'.1).comp (StdAdm.prodLatEquiv T T').surjective), fun g x => ?_⟩
  change i (q (latRep T.L g (StdAdm.prodLatEquiv T T' x).1)) + j (q' (latRep T'.L g (StdAdm.prodLatEquiv T T' x).2)) =
    C.ρ g (i (q (StdAdm.prodLatEquiv T T' x).1) + j (q' (StdAdm.prodLatEquiv T T' x).2))
  rw [hq.2, hq'.2, hi, hj, map_add]

theorem onto_one [IsDomain O] (hs : Function.Surjective (algebraMap O k)) (T : LocLat G Qp LL O) (e₀ : ↥T.L.T)
    (hρ : ∀ g x, T.ρ g x = x) (h0 : e₀ ≠ 0) (hsp : Submodule.span O {e₀} = ⊤) :
    ∃ q : ↥T.L.T →ₗ[O] (Fin 1 → k), Onto T (chr 1 : Ob k G) q ∧ q e₀ = fun _ => 1 := by
  have := T.L.free
  have hb : Function.Bijective (LinearMap.toSpanSingleton O ↥T.L.T e₀) := by
    refine ⟨smul_left_injective O h0, ?_⟩
    rw [← LinearMap.range_eq_top, ← LinearMap.span_singleton_eq_range, hsp]
  let e := LinearEquiv.ofBijective _ hb
  have he : e 1 = e₀ := one_smul O e₀
  refine ⟨(LinearMap.pi fun _ => Algebra.linearMap O k).comp e.symm.toLinearMap, ⟨?_, fun g x => ?_⟩, ?_⟩
  · intro y
    obtain ⟨c, hc⟩ := hs (y 0)
    refine ⟨e c, funext fun i => ?_⟩
    obtain rfl : i = 0 := Subsingleton.elim _ _
    change algebraMap O k (e.symm (e c)) = y 0
    rw [e.symm_apply_apply, hc]
  · have h1 : latRep T.L g x = x := Subtype.ext (hρ g x)
    rw [h1]
    exact (one_smul k _).symm
  · funext i
    change algebraMap O k (e.symm e₀) = 1
    rw [← he, e.symm_apply_apply, map_one]

theorem lattice_quotients : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL] [Algebra Qp LL] [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Algebra O LL] [TopologicalSpace LL] {k : Type} [Field k] [Algebra O k] (lam : O), algebraMap O LL lam ≠ 0 → algebraMap O k lam = 0 → Function.Surjective (algebraMap O k) → (∀ x, algebraMap O k x = 0 → lam ∣ x) → (∀ (A B : Ob k G) f, IsHom A B f → Function.Injective f → (∃ (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin B.m → k)), Onto T B q) → ∃ (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)), Onto T A q) ∧ (∀ (A B : Ob k G) f, IsHom A B f → Function.Surjective f → (∃ (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)), Onto T A q) → ∃ (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin B.m → k)), Onto T B q) ∧ (∀ (A B C : Ob k G) i j, IsHom A C i → IsHom B C j → Function.Surjective (i.coprod j) → (∃ (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)), Onto T A q) → (∃ (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin B.m → k)), Onto T B q) → ∃ (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin C.m → k)), Onto T C q) ∧ ∀ (T : LocLat G Qp LL O) (e₀ : ↥T.L.T), (∀ g x, T.ρ g x = x) → e₀ ≠ 0 → Submodule.span O {e₀} = ⊤ → ∃ q : ↥T.L.T →ₗ[O] (Fin 1 → k), Onto T (chr 1 : Ob k G) q ∧ q e₀ = fun _ => 1 := by
  intro G _ _ Qp LL O _ _ _ _ _ _ _ _ k _ _ lam hl hk hs _
  refine ⟨?_, ?_, ?_, onto_one hs⟩
  · rintro A B f hf hi ⟨T, q, hq⟩
    exact onto_sub lam hl hk A B f hf hi T q hq
  · rintro A B f hf hi ⟨T, q, hq⟩
    exact ⟨T, _, onto_quot A B f hf hi T q hq⟩
  · rintro A B C i j hi hj h ⟨T, q, hq⟩ ⟨T', q', hq'⟩
    exact ⟨_, _, onto_sum A B C i j hi hj h T q hq T' q' hq'⟩

end GlobalTheory.RedFun.LatQuot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCutCoboundaryModuleLeUnitDelta
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut
open GlobalTheory.Cut.Cob (length_inf_coboundaries_le_two_mul_rank inSpan_add inSpan_mul inSpan_scalar mat_ext map_smul_mulVec matKO_sum)

namespace GlobalTheory.Cut.CobOrd

variable {D : D7} {i : D.nd.Loc} {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))}
  {ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))} {π : D.nd.X i} {S : IdempotentChoiceData D.nd i}

theorem inR'_comp (hS : Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S) {a : D.nd.X i → MatN D.nd i} (ha : InR D.nd i r a) :
    InR' D.nd r S fun x' => a (S.p x') := by
  obtain ⟨-, -, -, -, -, -, -, ⟨hT, -⟩, -⟩ := hS
  obtain ⟨m, f, g, hf, rfl⟩ := ha
  exact ⟨m, fun k x' => f k (S.p x'), g, fun k => hT _ (hf k), by funext x'; simp only [Finset.sum_apply]⟩

theorem inR'_Eel (hS : Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S) : InR' D.nd r S (Eel D.nd S) := by
  have hB := inR'_comp hS hS.1.1
  have hX := inR'_comp hS hS.2.2.2.2.2.2.1.1
  have hr := hS.2.2.2.2.2.2.2.1.2.1
  have key : ∀ L : List ℕ, (∀ c ∈ L, c ∈ Finset.Icc 1 D.R.t) → InR' D.nd r S fun x' =>
      (L.map fun c => S.X0 (S.p x') - S.rr c x' • S.eB (S.p x')).prod := by
    intro L
    induction L with
    | nil => exact fun _ => Check.inR'_one i r S
    | cons c L ih =>
      intro h
      have h1 := inSpan_mul (inSpan_add hX (inSpan_mul (inSpan_scalar (neg_mem (hr c (h c (by simp))))) hB))
        (ih fun c hc => h c (by simp [hc]))
      refine Eq.mp (congrArg (InR' D.nd r S) ?_) h1
      funext x'
      simp [sub_eq_add_neg]
  refine key _ fun c hc => ?_
  rw [List.mem_range'_1] at hc
  rw [Finset.mem_Icc]
  omega

theorem del_mem (hS : Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S) : del51 D.nd S ∈ S.T' := by
  have hr := hS.2.2.2.2.2.2.2.1.2.1
  have : del51 D.nd S = ∏ c ∈ Finset.Ioc 1 D.R.t, (S.rr 1 - S.rr c) := by
    funext x'
    simp [del51, Finset.prod_apply]
  rw [this]
  refine prod_mem fun c hc => sub_mem (hr 1 ?_) (hr c ?_) <;>
  · rw [Finset.mem_Ioc] at hc
    rw [Finset.mem_Icc]
    omega

theorem del_smul_sum (hS : Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S) (Xs : Set (D.nd.X i)) {k : ℕ}
    (ψ : (S.X' → MatN D.nd i) → Matrix (Fin k) (Fin k) (D.nd.O i)) (hE : ψ (Eel D.nd S) = 0)
    (hψ : ∀ f ∈ S.T', ψ (fun x' => f x' • (1 : MatN D.nd i)) = f S.π' • 1)
    {m : ℕ} {f : Fin m → S.X' → D.nd.O i} {g : Fin m → GE D.nd} (hf : ∀ j, f j ∈ S.T')
    (e : Eel D.nd S = ∑ j, fun x' => f j x' • rO D.nd i r (S.p x') (g j))
    {c : GE D.nd → KOG (D.nd.O i) k} (hc : c ∈ cocW i r S Xs ψ) :
    del51 D.nd S S.π' • ∑ j, (((chiU D.nd i 1 (g j) : (D.nd.O i)ˣ) : D.nd.O i) * f j S.π') • c (g j) = 0 := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨φ, h1, -, rfl⟩ := hc
    have hE2 := hS.2.2.2.2.2.2.2.2.2.2.1.2.1
    let s : Fin m → S.X' → D.nd.O i := fun j => ((chiU D.nd i 1 (g j) : (D.nd.O i)ˣ) : D.nd.O i) • f j
    have hs : ∀ j, s j ∈ S.T' := fun j => S.T'.smul_mem (hf j) _
    let z : S.X' → MatN D.nd i := ∑ j, (fun x' => s j x' • (1 : MatN D.nd i)) * yg D.nd r S (g j)
    have hz : InY D.nd r S z := ⟨m, _, g, fun j => inSpan_scalar (hs j), rfl⟩
    have hz1 : ∀ x', z x' = (del51 D.nd S x' - ∑ j, s j x') • Eel D.nd S x' := by
      intro x'
      rw [sub_smul, ← hE2, Finset.sum_smul]
      nth_rewrite 1 [congrFun e x']
      simp only [z, Finset.sum_apply]
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Pi.mul_apply, yg, s, Pi.smul_apply, smul_eq_mul, smul_mul_assoc, one_mul, smul_sub, smul_smul]
      rw [mul_right_comm, Units.mul_inv, one_mul]
    have hz2 : Eel D.nd S * z = (fun x' => del51 D.nd S x' • (1 : MatN D.nd i)) * z := by
      funext x'
      simp only [Pi.mul_apply, hz1, mul_smul_comm, hE2, smul_mul_assoc, one_mul]
    have h2 := congrArg φ hz2
    rw [h1 _ (inR'_Eel hS) _ hz, h1 _ (inSpan_scalar (del_mem hS)) _ hz, hE, hψ _ (del_mem hS),
      Check.matKO_smul_one, ← zero_smul (D.nd.O i) (1 : Matrix (Fin k) (Fin k) (D.nd.O i)),
      Check.matKO_smul_one, zero_smul] at h2
    rw [h2]
    congr 1
    simp only [z, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [h1 _ (inSpan_scalar (hs j)) _ (Check.inY_yg i r S _), hψ _ (hs j), Check.matKO_smul_one]
    rfl
  | zero => simp
  | add a b _ _ ha hb => simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib, ha, hb, add_zero]
  | smul a b _ hb =>
    simp only [Pi.smul_apply, smul_comm _ a, ← Finset.smul_sum]
    rw [hb, smul_zero]

theorem psi_scalar (hS : Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S) {f : S.X' → D.nd.O i} (hf : f ∈ S.T') :
    S.ψρ (fun x' => f x' • (1 : MatN D.nd i)) = f S.π' • 1 ∧
      ∀ c, S.ψχ c (fun x' => f x' • (1 : MatN D.nd i)) = f S.π' := by
  have h := fun u => hS.2.2.1 _ (inSpan_scalar hf) (S.e.symm u)
  simp only [map_smul_mulVec, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec, map_smul,
    LinearEquiv.apply_symm_apply] at h
  refine ⟨mat_ext fun v => ?_, fun c => ?_⟩
  · rw [map_smul_mulVec, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
    exact (congrArg Prod.fst (h (v, 0))).symm
  · have := congrFun (congrArg Prod.snd (h (0, fun _ => 1))) c
    simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_one] at this
    exact (IsFractionRing.injective _ _ this).symm

theorem psi_Eel (hS : Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S) :
    S.ψρ (Eel D.nd S) = 0 ∧ ∀ c : Fin D.R.t, (c : ℕ) ≠ 0 → S.ψχ c (Eel D.nd S) = 0 := by
  have h := fun u => (hS.2.2.1 _ (inR'_Eel hS) (S.e.symm u)).symm.trans (hS.2.2.2.2.2.2.2.2.2.2.1.2.2.1 _)
  simp only [LinearEquiv.apply_symm_apply] at h
  refine ⟨mat_ext fun v => ?_, fun c hc => ?_⟩
  · rw [Matrix.map_zero _ (map_zero _), Matrix.zero_mulVec]
    exact congrArg Prod.fst (h (v, 0))
  · have := congrFun (congrArg Prod.snd (h (0, fun _ => 1))) c
    simp only [mul_one, if_neg hc] at this
    exact IsFractionRing.injective (D.nd.O i) (KK D.nd i) (this.trans (map_zero _).symm)

theorem sum_blocks (hS : Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S)
    {m : ℕ} {f : Fin m → S.X' → D.nd.O i} {g : Fin m → GE D.nd}
    (e : Eel D.nd S = ∑ j, fun x' => f j x' • rO D.nd i r (S.p x') (g j)) :
    ∑ j, f j S.π' • rhoO D.nd i ρ π (g j) = 0 ∧
      ∀ c : Fin D.R.t, ∑ j, f j S.π' * ((chiU D.nd i ((c : ℕ) + 1) (g j) : (D.nd.O i)ˣ) : D.nd.O i) =
        if (c : ℕ) = 0 then del51 D.nd S S.π' else 0 := by
  have hp : S.p S.π' = π := hS.2.2.2.2.2.2.2.2.2.1.1
  have hsum : ∀ {k : ℕ} (A : Fin m → Matrix (Fin k) (Fin k) (D.nd.O i)) (v : Fin k → KK D.nd i),
      ((∑ j, f j S.π' • A j).map (toK D.nd i)).mulVec v =
        ∑ j, toK D.nd i (f j S.π') • ((A j).map (toK D.nd i)).mulVec v := by
    intro k A v
    change ((toK D.nd i).mapMatrix _).mulVec v = _
    rw [map_sum, Matrix.sum_mulVec]
    exact Finset.sum_congr rfl fun j _ => map_smul_mulVec _ _ _
  have h1 : ∀ g u, S.e (((rO D.nd i r π g).map (toK D.nd i)).mulVec u) =
      (((rhoO D.nd i ρ π g).map (toK D.nd i)).mulVec (S.e u).1,
        fun c : Fin D.R.t => toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) * (S.e u).2 c) :=
    hS.2.1
  have h := fun u => hS.2.2.2.2.2.2.2.2.2.2.1.2.2.1 (S.e.symm u)
  rw [congrFun e S.π'] at h
  simp only [Finset.sum_apply, hp, hsum, map_sum, map_smul, h1, LinearEquiv.apply_symm_apply] at h
  refine ⟨mat_ext fun v => ?_, fun c => ?_⟩
  · rw [Matrix.map_zero _ (map_zero _), Matrix.zero_mulVec, hsum]
    have := congrArg Prod.fst (h (v, 0))
    rw [Prod.fst_sum] at this
    exact this
  · have := congrFun (congrArg Prod.snd (h (0, fun _ => 1))) c
    rw [Prod.snd_sum, Finset.sum_apply] at this
    simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_one] at this
    apply IsFractionRing.injective (D.nd.O i) (KK D.nd i)
    rw [apply_ite (algebraMap (D.nd.O i) (KK D.nd i)), map_zero, map_sum]
    simp only [map_mul]
    exact this

theorem del_sq_smul (hS : Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S) (Xs : Set (D.nd.X i)) {k : ℕ}
    (ψ : (S.X' → MatN D.nd i) → Matrix (Fin k) (Fin k) (D.nd.O i)) (hE : ψ (Eel D.nd S) = 0)
    (hψ : ∀ f ∈ S.T', ψ (fun x' => f x' • (1 : MatN D.nd i)) = f S.π' • 1)
    (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (hM : ∀ {m : ℕ} {f : Fin m → S.X' → D.nd.O i} {g : Fin m → GE D.nd},
      (Eel D.nd S = ∑ j, fun x' => f j x' • rO D.nd i r (S.p x') (g j)) →
      ∑ j, (((chiU D.nd i 1 (g j) : (D.nd.O i)ˣ) : D.nd.O i) * f j S.π') • M (g j) = 0)
    (w : KOG (D.nd.O i) k) (hw : d0 (WKG M) w ∈ cocW i r S Xs ψ) :
    (del51 D.nd S S.π' * del51 D.nd S S.π') • w = 0 := by
  obtain ⟨m, f, g, hf, e⟩ := inR'_Eel hS
  have h := del_smul_sum hS Xs ψ hE hψ hf e hw
  have h0 := (sum_blocks hS e).2 ⟨0, D.R.t_odd.pos⟩
  simp only [zero_add, if_true, mul_comm (f _ _)] at h0
  simp only [amitsur_d0_apply, smul_sub, Finset.sum_sub_distrib, Check.WKG_eq_matKO] at h
  rw [← matKO_sum, hM e, ← Finset.sum_smul, h0, ← zero_smul (D.nd.O i) (1 : Matrix (Fin k) (Fin k) (D.nd.O i)),
    Check.matKO_smul_one, zero_smul, smul_zero, zero_sub, neg_eq_zero, smul_smul] at h
  exact h

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S → π ∈ Xs → lenCob i (WpO D.nd i ρ π) (cocRho i r S Xs) ≤ ((2 * D.R.r : ℕ) : ℕ∞) * lenQ i (del51 D.nd S S.π') ∧ ∀ c : Fin D.R.t, lenCob i (chiRatO D.nd i ((c : ℕ) + 1)) (cocChi i r S Xs c) ≤ 2 * lenQ i (del51 D.nd S S.π') := by
  intro D i r ρ π Xs S _ hS _
  refine ⟨length_inf_coboundaries_le_two_mul_rank _ _ _ (del_sq_smul hS Xs _ (psi_Eel hS).1 (fun f hf => (psi_scalar hS hf).1) _ ?_),
    fun c => ?_⟩
  · intro m f g e
    rw [← (sum_blocks hS e).1]
    refine Finset.sum_congr rfl fun j _ => ?_
    change _ • ((((chiU D.nd i 1 (g j))⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) • rhoO D.nd i ρ π (g j)) = _
    rw [smul_smul, mul_right_comm, Units.mul_inv, one_mul]
  have hχ : ∀ g, chiRatO D.nd i ((c : ℕ) + 1) g =
      ((chiU D.nd i ((c : ℕ) + 1) g * (chiU D.nd i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) •
        (1 : Matrix (Fin 1) (Fin 1) (D.nd.O i)) := fun _ => rfl
  by_cases hc : (c : ℕ) = 0
  · have : ReciprocityTheory.Gal.B1 (WKG (chiRatO D.nd i ((c : ℕ) + 1))) = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨w, rfl⟩
      funext g
      change WKG _ g w - w = 0
      rw [Check.WKG_eq_matKO, hχ, Check.matKO_smul_one, hc, zero_add, mul_inv_cancel, Units.val_one, one_smul,
        sub_self]
    rw [lenCob, this, inf_bot_eq, Module.length_bot]
    exact zero_le
  · refine length_inf_coboundaries_le_two_mul_rank _ _ _ (del_sq_smul hS Xs _ ?_ (fun f hf => ?_) _ ?_)
    · simp only [(psi_Eel hS).2 c hc, zero_smul]
    · simp only [(psi_scalar hS hf).2 c]
    · intro m f g e
      have h := (sum_blocks hS e).2 c
      rw [if_neg hc] at h
      simp only [hχ, smul_smul]
      rw [← Finset.sum_smul]
      convert zero_smul (D.nd.O i) (1 : Matrix (Fin 1) (Fin 1) (D.nd.O i))
      rw [← h]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Units.val_mul, mul_mul_mul_comm, mul_comm _ ((chiU D.nd i ((c : ℕ) + 1) (g j) : (D.nd.O i)ˣ) : D.nd.O i)]
      have := (chiU D.nd i 1 (g j)).mul_inv
      linear_combination (f j S.π' * ((chiU D.nd i ((c : ℕ) + 1) (g j) : (D.nd.O i)ˣ) : D.nd.O i)) * this

end GlobalTheory.Cut.CobOrd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalisedGlobalCocyclesInLocalSpanStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localised_global_cocycles_in_local_span : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → GoodCongruenceObjects D.nd r ρ π S → π ∈ Xs → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), (∀ f ∈ cocRho i r S Xs, InCut i r Xs (WpO D.nd i ρ π) w hw f) ∧ ∀ c : Fin D.R.t, ∀ f ∈ cocChi i r S Xs c, InCut i r Xs (chiRatO D.nd i ((c : ℕ) + 1)) w hw f := by
  first | exact @GlobalTheory.Cut.LocCoc.main | exact GlobalTheory.Cut.LocCoc.main | (intros; apply GlobalTheory.Cut.LocCoc.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeOfFrobeniusEquationCyclotomicFixedStatement
section
set_option synthInstance.maxHeartbeats 400000
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_range_of_frobeniusEquation_cyclotomicFixed : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))) (E : EtSit P AI K s LL h W) (ι : Type) [Fintype ι] (M : ι → ι → W.EE) (c : ι → W.EE) (w : ι → RW LL), (∀ g : ↥(GK K), W.resΓ g = 1 → ∀ i, AI.gRW LL (g : GQ l) (w i) = w i) → (∀ i, w i = ∑ j, E.tie.ioE (M i j) * φRW LL (w j) + E.tie.ioE (c i)) → ∀ i, ∃ e : W.EE, E.tie.ioE e = w i := by
  first | exact @GlobalTheory.FrobDescent.mem_range_of_fixed | exact GlobalTheory.FrobDescent.mem_range_of_fixed | (intros; apply GlobalTheory.FrobDescent.mem_range_of_fixed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiFreeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_decomposition_one_add_X_pow_mul_phi : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Algebra ℤ_[l] O], (l : O) ≠ 0 → ¬ IsUnit (l : O) → ∀ y : PowerSeries O, ∃! z : Fin l → PowerSeries O, y = ∑ j : Fin l, (1 + PowerSeries.X) ^ (j : ℕ) * phi l O (z j) := by
  first | exact @GlobalTheory.Cyc.phi_free | exact GlobalTheory.Cyc.phi_free | (intros; apply GlobalTheory.Cyc.phi_free <;> assumption)
end


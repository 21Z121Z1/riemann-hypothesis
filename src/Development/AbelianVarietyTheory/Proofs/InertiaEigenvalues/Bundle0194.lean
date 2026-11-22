import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0185
import Formalism.WachLatticeTwists.LatticeDualFibres.FibreDualStable
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0054
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0171
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0187
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0173
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0186
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0049
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0051
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0087
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussAtUniformiser
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0085
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersEqSumZetaPow
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KillsCokerAllOfKillsCokerPhiModuleLattice
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSeriesOfExact
section
noncomputable section

namespace GlobalTheory.AdmLoc

section Ss

variable {R : Type} [Ring R]
variable {M M' A A' C C' : Type} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
  [AddCommGroup A] [Module R A] [AddCommGroup A'] [Module R A']
  [AddCommGroup C] [Module R C] [AddCommGroup C'] [Module R C']

theorem subquot_map {f : A →ₗ[R] M} (hf : Function.Injective f) (X Y : Submodule R A) {X' Y' : Submodule R M}
    (hX : X' = X.map f) (hY : Y' = Y.map f) :
    Nonempty ((↥Y ⧸ X.comap Y.subtype) ≃ₗ[R] (↥Y' ⧸ X'.comap Y'.subtype)) := by
  subst hX hY
  refine ⟨Submodule.Quotient.equiv _ _ (Submodule.equivMapOfInjective f hf Y) ?_⟩
  ext ⟨y, hy⟩
  constructor
  · rintro ⟨x, hx, hxy⟩
    exact ⟨x, hx, congrArg Subtype.val hxy⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨x', hx', hxx⟩ := hy
    obtain rfl : x' = x := hf hxx
    exact ⟨⟨x', hx'⟩, hx, rfl⟩

theorem subquot_comap {g : M →ₗ[R] C} (hg : Function.Surjective g) (X Y : Submodule R C) {X' Y' : Submodule R M}
    (hX : X' = X.comap g) (hY : Y' = Y.comap g) :
    Nonempty ((↥Y ⧸ X.comap Y.subtype) ≃ₗ[R] (↥Y' ⧸ X'.comap Y'.subtype)) := by
  subst hX hY
  let p : ↥(Y.comap g) →ₗ[R] ↥Y := g.restrict (fun _ h => h)
  let q : ↥(Y.comap g) →ₗ[R] (↥Y ⧸ X.comap Y.subtype) := (Submodule.mkQ _).comp p
  have hp : Function.Surjective p := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hg y
    exact ⟨⟨x, hy⟩, rfl⟩
  have hq : Function.Surjective q := (Submodule.mkQ_surjective _).comp hp
  have hk : (X.comap g).comap (Y.comap g).subtype = LinearMap.ker q := by
    ext x
    exact (Submodule.Quotient.mk_eq_zero (X.comap Y.subtype) (x := p x)).symm
  exact ⟨((Submodule.quotEquivOfEq _ _ hk).trans (q.quotKerEquivOfSurjective hq)).symm⟩

theorem exists_series_of_exact {f : A →ₗ[R] M} {g : M →ₗ[R] C} (hf : Function.Injective f)
    (hg : Function.Surjective g) (H : Function.Exact f g)
    (t : CompositionSeries (Submodule R A)) (ht₁ : t.head = ⊥) (ht₂ : t.last = ⊤)
    (s : CompositionSeries (Submodule R C)) (hs₁ : s.head = ⊥) (hs₂ : s.last = ⊤) :
    ∃ r : CompositionSeries (Submodule R M), r.head = ⊥ ∧ r.last = ⊤ ∧
      ∃ e : Fin t.length ⊕ Fin s.length ≃ Fin r.length,
        (∀ i, Nonempty (factor t i ≃ₗ[R] factor r (e (Sum.inl i)))) ∧
        ∀ j, Nonempty (factor s j ≃ₗ[R] factor r (e (Sum.inr j))) := by
  let s' : CompositionSeries (Submodule R M) :=
    { length := s.length
      toFun := fun i => (s i).comap g
      step := fun i => Submodule.comap_covBy_of_surjective hg (s.step i) }
  let t' : CompositionSeries (Submodule R M) :=
    { length := t.length
      toFun := fun i => (t i).map f
      step := fun i => Submodule.map_covBy_of_injective hf (t.step i) }
  have hc : t'.last = s'.head := by
    change t.last.map f = s.head.comap g
    rw [ht₂, hs₁, Submodule.map_top, Submodule.comap_bot, LinearMap.exact_iff.mp H]
  refine ⟨t'.smash s' hc, ?_, ?_, finSumFinEquiv, fun i => ?_, fun j => ?_⟩
  · rw [RelSeries.head_smash]
    change t.head.map f = ⊥
    rw [ht₁, Submodule.map_bot]
  · rw [RelSeries.last_smash]
    change s.last.comap g = ⊤
    rw [hs₂, Submodule.comap_top]
  · exact subquot_map hf _ _ (RelSeries.smash_castAdd hc i) (RelSeries.smash_succ_castAdd hc i)
  · exact subquot_comap hg _ _ (RelSeries.smash_natAdd hc j) (RelSeries.smash_succ_natAdd hc j)

theorem SameFactors.finiteLength_left (h : SameFactors R M M') : IsFiniteLength R M := by
  obtain ⟨s, -, h1, h2, -⟩ := h
  exact isFiniteLength_of_exists_compositionSeries ⟨s, h1, h2⟩

theorem SameFactors.finiteLength_right (h : SameFactors R M M') : IsFiniteLength R M' :=
  h.symm.finiteLength_left

theorem SameFactors.of_exact_of_exact {f : A →ₗ[R] M} {g : M →ₗ[R] C} (hf : Function.Injective f)
    (hg : Function.Surjective g) (H : Function.Exact f g)
    {f' : A' →ₗ[R] M'} {g' : M' →ₗ[R] C'} (hf' : Function.Injective f')
    (hg' : Function.Surjective g') (H' : Function.Exact f' g')
    (hA : SameFactors R A A') (hC : SameFactors R C C') : SameFactors R M M' := by
  obtain ⟨t, t', ht1, ht2, ht3, ht4, a, ha⟩ := hA
  obtain ⟨s, s', hs1, hs2, hs3, hs4, c, hc⟩ := hC
  obtain ⟨r, hr1, hr2, e, he1, he2⟩ := exists_series_of_exact hf hg H t ht1 ht2 s hs1 hs2
  obtain ⟨r', hr3, hr4, e', he3, he4⟩ := exists_series_of_exact hf' hg' H' t' ht3 ht4 s' hs3 hs4
  refine ⟨r, r', hr1, hr2, hr3, hr4, e.symm.trans ((a.sumCongr c).trans e'), fun k => ?_⟩
  obtain ⟨k, rfl⟩ := e.surjective k
  rw [Equiv.trans_apply, Equiv.symm_apply_apply]
  rcases k with i | j
  · obtain ⟨u⟩ := he1 i
    obtain ⟨v⟩ := ha i
    obtain ⟨w⟩ := he3 (a i)
    exact ⟨(u.symm.trans v).trans w⟩
  · obtain ⟨u⟩ := he2 j
    obtain ⟨v⟩ := hc j
    obtain ⟨w⟩ := he4 (c j)
    exact ⟨(u.symm.trans v).trans w⟩

theorem SameFactors.of_exact {f : A →ₗ[R] M} {g : M →ₗ[R] C} (hf : Function.Injective f)
    (hg : Function.Surjective g) (H : Function.Exact f g) (h : IsFiniteLength R M) :
    SameFactors R M (A × C) :=
  SameFactors.of_exact_of_exact hf hg H LinearMap.inl_injective LinearMap.snd_surjective .inl_snd
    (SameFactors.refl (h.of_injective hf)) (SameFactors.refl (h.of_surjective hg))

theorem SameFactors.sub_prod_quot (h : IsFiniteLength R M) (S : Submodule R M) :
    SameFactors R M (↥S × (M ⧸ S)) :=
  SameFactors.of_exact S.subtype_injective S.mkQ_surjective (LinearMap.exact_subtype_mkQ S) h

theorem SameFactors.prod (hA : SameFactors R A A') (hC : SameFactors R C C') :
    SameFactors R (A × C) (A' × C') :=
  SameFactors.of_exact_of_exact LinearMap.inl_injective LinearMap.snd_surjective .inl_snd
    LinearMap.inl_injective LinearMap.snd_surjective .inl_snd hA hC

theorem SameFactors.congr (h : SameFactors R A A') (e : A ≃ₗ[R] C) (e' : A' ≃ₗ[R] C') : SameFactors R C C' :=
  ((SameFactors.of_equiv h.finiteLength_left e).symm.trans h).trans (SameFactors.of_equiv h.finiteLength_right e')

theorem SameFactors.of_subsingleton [Subsingleton A] [Subsingleton A'] : SameFactors R A A' :=
  SameFactors.of_equiv IsFiniteLength.of_subsingleton (LinearEquiv.ofSubsingleton _ _)

theorem SameFactors.pi_fin : ∀ {m : ℕ} {N N' : Fin m → Type} [∀ j, AddCommGroup (N j)] [∀ j, Module R (N j)]
    [∀ j, AddCommGroup (N' j)] [∀ j, Module R (N' j)], (∀ j, SameFactors R (N j) (N' j)) →
    SameFactors R (∀ j, N j) (∀ j, N' j)
  | 0, _, _, _, _, _, _, _ => SameFactors.of_subsingleton
  | _ + 1, N, N', _, _, _, _, h =>
    ((h 0).prod (SameFactors.pi_fin fun j => h (Fin.succ j))).congr
      (Fin.consLinearEquiv R N) (Fin.consLinearEquiv R N')

theorem SameFactors.pi {ι : Type} [Finite ι] {N N' : ι → Type} [∀ j, AddCommGroup (N j)] [∀ j, Module R (N j)]
    [∀ j, AddCommGroup (N' j)] [∀ j, Module R (N' j)] (h : ∀ j, SameFactors R (N j) (N' j)) :
    SameFactors R (∀ j, N j) (∀ j, N' j) := by
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  exact (SameFactors.pi_fin (N := fun j => N (e.symm j)) (N' := fun j => N' (e.symm j))
    fun j => h (e.symm j)).congr (LinearEquiv.piCongrLeft R N e.symm) (LinearEquiv.piCongrLeft R N' e.symm)

theorem SameFactors.prod_comm (hA : IsFiniteLength R A) (hC : IsFiniteLength R C) :
    SameFactors R (A × C) (C × A) :=
  ((SameFactors.refl hA).prod (SameFactors.refl hC)).congr (LinearEquiv.refl _ _) (LinearEquiv.prodComm R A C)

end Ss

section Rep

variable {O G : Type} [CommRing O] [Group G]
variable {M M' A A' C C' : Type} [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
  [AddCommGroup A] [Module O A] [AddCommGroup A'] [Module O A']
  [AddCommGroup C] [Module O C] [AddCommGroup C'] [Module O C']

def asModuleMap {π : Representation O G M} {π' : Representation O G M'} (f : M →ₗ[O] M')
    (hf : ∀ g x, f (π g x) = π' g (f x)) : π.asModule →ₗ[MonoidAlgebra O G] π'.asModule :=
  Representation.IntertwiningMap.equivLinearMapAsModule π π'
    { toLinearMap := f, isIntertwining' := fun g => LinearMap.ext (hf g) }

theorem asModuleMap_apply {π : Representation O G M} {π' : Representation O G M'} (f : M →ₗ[O] M')
    (hf : ∀ g x, f (π g x) = π' g (f x)) (x : π.asModule) :
    π'.asModuleEquiv (asModuleMap f hf x) = f (π.asModuleEquiv x) := rfl

def equivAsModule {π : Representation O G M} {π' : Representation O G M'} (e : M ≃ₗ[O] M')
    (he : ∀ g x, e (π g x) = π' g (e x)) : π.asModule ≃ₗ[MonoidAlgebra O G] π'.asModule :=
  LinearEquiv.ofBijective (asModuleMap e.toLinearMap he) e.bijective

def piAsModule {ι : Type} {N : ι → Type} [∀ j, AddCommGroup (N j)] [∀ j, Module O (N j)]
    (π : ∀ j, Representation O G (N j)) :
    (piRep π).asModule ≃ₗ[MonoidAlgebra O G] ∀ j, (π j).asModule :=
  LinearEquiv.ofBijective
    (LinearMap.pi fun j => asModuleMap (π := piRep π) (π' := π j) (LinearMap.proj j) fun _ _ => rfl)
    (Function.bijective_id (α := ∀ j, N j))

theorem finiteLength_asModule (π : Representation O G M) (h : IsFiniteLength O M) :
    IsFiniteLength (MonoidAlgebra O G) π.asModule := by
  have h' : IsFiniteLength O π.asModule := h.of_injective (f := π.asModuleEquiv.toLinearMap) π.asModuleEquiv.injective
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at h' ⊢
  exact ⟨isNoetherian_of_tower O h'.1, isArtinian_of_tower O h'.2⟩

variable {π : Representation O G M} {π' : Representation O G M'} {α : Representation O G A}
  {α' : Representation O G A'} {γ : Representation O G C} {γ' : Representation O G C'}

theorem SameSS.refl' (h : IsFiniteLength (MonoidAlgebra O G) π.asModule) : SameSS π π := SameFactors.refl h

theorem SameSS.refl (π : Representation O G M) (h : IsFiniteLength O M) : SameSS π π :=
  SameFactors.refl (finiteLength_asModule π h)

theorem SameSS.symm (h : SameSS π π') : SameSS π' π := SameFactors.symm h

theorem SameSS.trans (h : SameSS π π') (h' : SameSS π' α) : SameSS π α := SameFactors.trans h h'

theorem SameSS.of_equiv (h : IsFiniteLength O M) (e : M ≃ₗ[O] M') (he : ∀ g x, e (π g x) = π' g (e x)) :
    SameSS π π' :=
  SameFactors.of_equiv (finiteLength_asModule π h) (equivAsModule e he)

theorem SameSS.congr (h : SameSS α α') (e : A ≃ₗ[O] C) (he : ∀ g x, e (α g x) = γ g (e x))
    (e' : A' ≃ₗ[O] C') (he' : ∀ g x, e' (α' g x) = γ' g (e' x)) : SameSS γ γ' :=
  SameFactors.congr h (equivAsModule e he) (equivAsModule e' he')

theorem SameSS.congr_left (h : SameSS α π) (e : A ≃ₗ[O] C) (he : ∀ g x, e (α g x) = γ g (e x)) : SameSS γ π :=
  h.congr e he (LinearEquiv.refl O M) fun _ _ => rfl

theorem SameSS.congr_right (h : SameSS π α) (e : A ≃ₗ[O] C) (he : ∀ g x, e (α g x) = γ g (e x)) : SameSS π γ :=
  h.congr (LinearEquiv.refl O M) (fun _ _ => rfl) e he

theorem SameSS.of_exact_of_exact {f : A →ₗ[O] M} {p : M →ₗ[O] C}
    (ef : ∀ g x, f (α g x) = π g (f x)) (ep : ∀ g x, p (π g x) = γ g (p x))
    (hf : Function.Injective f) (hp : Function.Surjective p) (H : Function.Exact f p)
    {f' : A' →ₗ[O] M'} {p' : M' →ₗ[O] C'}
    (ef' : ∀ g x, f' (α' g x) = π' g (f' x)) (ep' : ∀ g x, p' (π' g x) = γ' g (p' x))
    (hf' : Function.Injective f') (hp' : Function.Surjective p') (H' : Function.Exact f' p')
    (hA : SameSS α α') (hC : SameSS γ γ') : SameSS π π' :=
  SameFactors.of_exact_of_exact (R := MonoidAlgebra O G) (M := π.asModule) (M' := π'.asModule)
    (A := α.asModule) (A' := α'.asModule) (C := γ.asModule) (C' := γ'.asModule)
    (f := asModuleMap f ef) (g := asModuleMap p ep) hf hp H
    (f' := asModuleMap f' ef') (g' := asModuleMap p' ep') hf' hp' H' hA hC

theorem SameSS.of_exact' {f : A →ₗ[O] M} {p : M →ₗ[O] C}
    (ef : ∀ g x, f (α g x) = π g (f x)) (ep : ∀ g x, p (π g x) = γ g (p x))
    (hf : Function.Injective f) (hp : Function.Surjective p) (H : Function.Exact f p)
    (h : IsFiniteLength (MonoidAlgebra O G) π.asModule) : SameSS π (α.prod γ) :=
  SameSS.of_exact_of_exact ef ep hf hp H (f' := LinearMap.inl O A C) (p' := LinearMap.snd O A C)
    (α' := α) (γ' := γ) (fun g x => by simp) (fun g x => by simp)
    LinearMap.inl_injective LinearMap.snd_surjective .inl_snd
    (SameSS.refl' (IsFiniteLength.of_injective (M := α.asModule) (N := π.asModule) (f := asModuleMap f ef) h hf))
    (SameSS.refl' (IsFiniteLength.of_surjective (M := π.asModule) (N := γ.asModule) (f := asModuleMap p ep) h hp))

theorem SameSS.of_exact {f : A →ₗ[O] M} {p : M →ₗ[O] C}
    (ef : ∀ g x, f (α g x) = π g (f x)) (ep : ∀ g x, p (π g x) = γ g (p x))
    (hf : Function.Injective f) (hp : Function.Surjective p) (H : Function.Exact f p)
    (h : IsFiniteLength O M) : SameSS π (α.prod γ) :=
  SameSS.of_exact' ef ep hf hp H (finiteLength_asModule π h)

theorem SameSS.prod (hA : SameSS α α') (hC : SameSS γ γ') : SameSS (α.prod γ) (α'.prod γ') :=
  SameSS.of_exact_of_exact (f := LinearMap.inl O A C) (p := LinearMap.snd O A C)
    (fun g x => by simp) (fun g x => by simp) LinearMap.inl_injective LinearMap.snd_surjective .inl_snd
    (f' := LinearMap.inl O A' C') (p' := LinearMap.snd O A' C')
    (fun g x => by simp) (fun g x => by simp) LinearMap.inl_injective LinearMap.snd_surjective .inl_snd hA hC

theorem SameSS.piRep {ι : Type} [Finite ι] {N N' : ι → Type} [∀ j, AddCommGroup (N j)] [∀ j, Module O (N j)]
    [∀ j, AddCommGroup (N' j)] [∀ j, Module O (N' j)] {σ : ∀ j, Representation O G (N j)}
    {σ' : ∀ j, Representation O G (N' j)} (h : ∀ j, SameSS (σ j) (σ' j)) : SameSS (piRep σ) (piRep σ') :=
  (SameFactors.pi (N := fun j => (σ j).asModule) (N' := fun j => (σ' j).asModule) h).congr
    (piAsModule σ).symm (piAsModule σ').symm

end Rep

end GlobalTheory.AdmLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinitePowSmulTorsionLatticeQuotientStatement
section
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_pow_smul_torsion_lattice_quotient : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] {V : Type} [AddCommGroup V] [Module O V] [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V] (T : Submodule O V), IsTopologicalRing O → CompactSpace O → IsAdic (IsLocalRing.maximalIdeal O) → IsLatticeIn T → ∀ ϖ : O, Irreducible ϖ → ∀ n : ℕ, Finite ↥(LinearMap.ker (LinearMap.lsmul O (V ⧸ T) (ϖ ^ n))) := by
  first | exact @GlobalTheory.LatTorsFinite.finite_ker_pow_smul | exact GlobalTheory.LatTorsFinite.finite_ker_pow_smul | (intros; apply GlobalTheory.LatTorsFinite.finite_ker_pow_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteSemisimple
section
open Formalism.MainNotions.N GlobalTheory.PsChar

namespace GlobalTheory.PsChar

theorem finite_semisimple (k R : Type) [Field k] [CharZero k] [IsAlgClosed k] [Ring R] [Algebra k R]
    (d : ℕ) (T : R →ₗ[k] k) (h : IsPsChar d (fun x => T x))
    (hnd : ∀ x, (∀ y, T (x * y) = 0) → x = 0) :
    Module.Finite k R ∧ IsSemisimpleRing R := by
  refine GlobalTheory.T.finite_and_isSemisimpleRing_of_no_nil_ideals_bounded_idempotents k R d (fun x => ?_) (fun x hx => ?_) (fun m e he hne => ?_)
  · obtain ⟨p, hp, -, hT⟩ := cayleyHamilton k R d T h x
    exact ⟨p, hp, hnd _ hT⟩
  · refine hnd x fun y => ?_
    rw [show T (x * y) = T (y * x) from h.comm x y]
    exact GlobalTheory.T.pseudoCharacter_eq_zero_of_isNilpotent k R d T h _ (hx y)
  · have hv : ∀ i, ∃ a : ℕ, 1 ≤ a ∧ T (e i) = a := fun i => by
      obtain ⟨⟨a, -, ha⟩, h0⟩ := GlobalTheory.T.pseudoCharacter_apply_idempotent_nat_le k R d T h (e i) (he.idem i)
      refine ⟨a, Nat.one_le_iff_ne_zero.2 fun h' => hne i (hnd _ (h0 ?_)), ha⟩
      rw [ha, h', Nat.cast_zero]
    choose a ha1 ha using hv
    obtain ⟨⟨s, hs, hsT⟩, -⟩ := GlobalTheory.T.pseudoCharacter_apply_idempotent_nat_le k R d T h (∑ i, e i) he.isIdempotentElem_sum
    have h1 : ((∑ i, a i : ℕ) : k) = s := by
      rw [← hsT, map_sum]; push_cast; exact Finset.sum_congr rfl fun i _ => (ha i).symm
    have h2 : ∑ i, a i = s := by exact_mod_cast h1
    calc m = ∑ _i : Fin m, 1 := by simp
      _ ≤ ∑ i, a i := Finset.sum_le_sum fun i _ => ha1 i
      _ = s := h2
      _ ≤ d := hs

def traceKer {k A : Type} [Field k] [Ring A] [Algebra k A] (T : A →ₗ[k] k)
    (hc : ∀ x y, T (x * y) = T (y * x)) : TwoSidedIdeal A :=
  TwoSidedIdeal.mk' {x | ∀ y, T (x * y) = 0} (by simp)
    (fun {x y} hx hy z => by simp only [Set.mem_setOf_eq] at hx hy; simp [add_mul, hx z, hy z])
    (fun {x} hx z => by simp only [Set.mem_setOf_eq] at hx; simp [neg_mul, hx z])
    (fun {x y} hy z => by
      simp only [Set.mem_setOf_eq] at hy
      rw [mul_assoc, hc, mul_assoc, hy])
    (fun {x y} hx z => by simp only [Set.mem_setOf_eq] at hx; rw [mul_assoc, hx])

theorem mem_traceKer {k A : Type} [Field k] [Ring A] [Algebra k A] (T : A →ₗ[k] k)
    (hc : ∀ x y, T (x * y) = T (y * x)) (x : A) : x ∈ traceKer T hc ↔ ∀ y, T (x * y) = 0 :=
  TwoSidedIdeal.mem_mk' _ _ _ _ _ _ x

theorem exists_descend {k A B : Type} [Field k] [AddCommGroup A] [Module k A] [AddCommGroup B]
    [Module k B] (f : A →ₗ[k] B) (hf : Function.Surjective f) (T : A →ₗ[k] k)
    (h : ∀ a, f a = 0 → T a = 0) : ∃ S : B →ₗ[k] k, ∀ a, S (f a) = T a := by
  refine ⟨(LinearMap.ker f).liftQ T (fun a ha => h a ha) ∘ₗ (f.quotKerEquivOfSurjective hf).symm.toLinearMap,
    fun a => ?_⟩
  have : (f.quotKerEquivOfSurjective hf).symm (f a) = Submodule.Quotient.mk a := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, this]
  exact Submodule.liftQ_apply _ _ _

theorem exists_ssRep (Γ k : Type) [Group Γ] [Field k] [CharZero k] [IsAlgClosed k] (d : ℕ)
    (T : Γ → k) (hT : IsPsChar d T) :
    ∃ r : Γ →* GL (Fin d) k, IsSSRep r ∧
      ∀ g, ((r g : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).trace = T g := by
  obtain ⟨T', hT'g, hT'⟩ := exists_linear_extension Γ k d T hT
  have hc : ∀ x y, T' (x * y) = T' (y * x) := hT'.comm
  let I := traceKer T' hc
  let f : MonoidAlgebra k Γ →ₐ[k] I.ringCon.Quotient := RingCon.mkₐ k I.ringCon
  have hf : Function.Surjective f := fun y => Quotient.inductionOn' y fun x => ⟨x, rfl⟩
  have hk : ∀ x, f x = 0 ↔ x ∈ I := fun x => by
    rw [TwoSidedIdeal.mem_iff, ← RingCon.eq]
    rfl
  obtain ⟨S, hS⟩ := exists_descend f.toLinearMap hf T' fun a ha => by
    simpa using (mem_traceKer T' hc a).1 ((hk a).1 ha) 1
  have hS1 : ∀ a, S (f a) = T' a := hS
  have hS' : IsPsChar d (fun x => S x) := by
    refine ⟨?_, ?_, ?_⟩
    · show S 1 = d
      rw [← map_one f, hS1]; exact hT'.one
    · intro x y
      obtain ⟨a, rfl⟩ := hf x
      obtain ⟨b, rfl⟩ := hf y
      show S (f a * f b) = S (f b * f a)
      rw [← map_mul, ← map_mul, hS1, hS1]; exact hc a b
    · intro x
      choose a ha using fun i => hf (x i)
      have hx : x = fun i => (f : MonoidAlgebra k Γ →* I.ringCon.Quotient) (a i) := funext fun i => (ha i).symm
      rw [hx, alt_comp_monoidHom]
      have he : (fun g => S ((f : MonoidAlgebra k Γ →* I.ringCon.Quotient) g)) = fun g => T' g :=
        funext fun g => hS1 g
      rw [he]; exact hT'.alt_eq_zero a
  have hnd : ∀ x, (∀ y, S (x * y) = 0) → x = 0 := by
    intro x hx
    obtain ⟨a, rfl⟩ := hf x
    refine (hk a).2 ((mem_traceKer T' hc a).2 fun b => ?_)
    rw [← hS1, map_mul]; exact hx (f b)
  obtain ⟨hfin, hss⟩ := finite_semisimple k _ d S hS' hnd
  obtain ⟨N, n, hn, ⟨e⟩⟩ := IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed k I.ringCon.Quotient
  let τ : (Π i, Matrix (Fin (n i)) (Fin (n i)) k) →ₗ[k] k := S ∘ₗ e.symm.toLinearMap
  have hτ : ∀ x, τ x = S (e.symm x) := fun x => rfl
  obtain ⟨c, hcτ⟩ := GlobalTheory.T.exists_eq_sum_trace_of_trace_like_pi_matrix k N n τ fun x y => by
    rw [hτ, hτ, map_mul e.symm, map_mul e.symm]; exact hS'.comm _ _
  have hcn : ∀ i, ∃ m : ℕ, c i = m := by
    intro i
    haveI := hn i
    let E : Π j, Matrix (Fin (n j)) (Fin (n j)) k := Pi.single i (Matrix.single 0 0 1)
    have hE : IsIdempotentElem E := by
      unfold IsIdempotentElem
      ext1 j
      by_cases hj : j = i
      · subst hj; simp [E, Matrix.single_mul_single_same]
      · simp [E, hj]
    have hτE : τ E = c i := by
      rw [hcτ, Finset.sum_eq_single i]
      · simp [E, Matrix.trace_single_eq_same]
      · intro j _ hj; simp [E, hj]
      · simp
    obtain ⟨⟨m, -, hm⟩, -⟩ := GlobalTheory.T.pseudoCharacter_apply_idempotent_nat_le k _ d S hS' (e.symm E) (hE.map e.symm)
    exact ⟨m, hτE.symm.trans hm⟩
  choose m hm using hcn
  have hsum : ∑ i, m i * n i = d := by
    have h1 : τ 1 = d := by rw [hτ, map_one]; exact hS'.one
    rw [hcτ] at h1
    simp only [Pi.one_apply, Matrix.trace_one, Fintype.card_fin, hm] at h1
    exact_mod_cast h1
  obtain ⟨ρ₀, hρ₀⟩ := GlobalTheory.T.exists_algHom_trace_eq_sum_mul_trace k N n m d hsum
  let g : I.ringCon.Quotient →ₐ[k] Matrix (Fin d) (Fin d) k := ρ₀.comp e.toAlgHom
  let ρ : MonoidAlgebra k Γ →ₐ[k] Matrix (Fin d) (Fin d) k := g.comp f
  have htr : ∀ a, (ρ a).trace = T' a := fun a => by
    show (ρ₀ (e (f a))).trace = _
    rw [hρ₀, ← hS1, ← e.symm_apply_apply (f a), ← hτ, hcτ]
    simp [hm]
  have hrange : IsSemisimpleRing ρ.range := by
    have : ρ.range = g.range := by
      rw [AlgHom.range_comp, (AlgHom.range_eq_top f).2 hf, Algebra.map_top]
    rw [this]
    exact RingHom.isSemisimpleRing_of_surjective g.rangeRestrict.toRingHom
      (AlgHom.rangeRestrict_surjective _)
  refine ⟨(ρ.toMonoidHom.comp (MonoidAlgebra.of k Γ)).toHomUnits, GlobalTheory.T.isSemisimpleRep_of_isSemisimpleRing_range Γ k d ρ hrange,
    fun x => ?_⟩
  show (ρ (MonoidAlgebra.of k Γ x)).trace = T x
  rw [htr, hT'g]

end GlobalTheory.PsChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FourierDescendedFunctionEqPartialFourierStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_descendedFunction_eq_partialFourier : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (r : ℕ) (M : Meas r F E) (x : A.K) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → ∀ μ : Measure A.L, SelfDual μ (A.kerL ψ x) → ∀ (Ax : selfAdjoint (Matrix (Fin r) (Fin r) E)) (lam : F) (α : Matrix.unitaryGroup (Fin r) E → ℝ), IsLocallyConstant α → HasCompactSupport α → ∀ f : Hn r F E → ℂ, IsTest f → fourB μ (A.kerL ψ x) (A.descFn M Ax j lam α f) = A.descFn M Ax j lam α (fourU M ψ f) := by
  first | exact @GlobalTheory.JR.fourB_descFn | exact GlobalTheory.JR.fourB_descFn | (intros; apply GlobalTheory.JR.fourB_descFn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussAtUniformiserStatement
section
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonNorm_uniformizer_isStableGauss : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ G₁ : ℂ, IsStableGauss A ψ x μ 1 G₁ → ∃ ϖ : A.Kˣ, (¬ ∃ y, A.NL y = ϖ) ∧ IsStableGauss A ψ x μ ϖ (-(G₁ * ((A.absK ϖ : ℂ))⁻¹)) := by
  first | exact @GlobalTheory.JR.WeilQuad.NonNorm.gauss_at_uniformiser | exact GlobalTheory.JR.WeilQuad.NonNorm.gauss_at_uniformiser | (intros; apply GlobalTheory.JR.WeilQuad.NonNorm.gauss_at_uniformiser <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsTerFurther
section
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

theorem φc_tc (l : ℕ) [Fact l.Prime] (y : Formalism.Per.Fl l) : φc l (tc l y) = tc l (y ^ l) := by
  unfold φc tc
  rw [(GlobalTheory.CrisMaps.phiA_extends l).alg]
  congr 1
  rw [GlobalTheory.RingBasics.φA_apply, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def]

theorem frob_teich : ∀ (l : ℕ) [Fact l.Prime] (y : Formalism.Per.Fl l), φc l (tc l y) = tc l (y ^ l) :=
  fun l _ y => φc_tc l y

end GlobalTheory.PMon.Gauss
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersEqSumZetaPowStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integers_eq_sum_zeta_pow_unique : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (i : ℕ), 2 ≤ i → ∀ ζ : Om l, IsPrimitiveRoot ζ (l ^ i) → (∀ x : Om l, x ∈ Ks K i → ‖x‖ ≤ 1 → ∃ y : Fin l → Om l, (∀ a, y a ∈ Ks K (i - 1) ∧ ‖y a‖ ≤ 1) ∧ x = ∑ a : Fin l, ζ ^ (a : ℕ) * y a) ∧ ∀ y : Fin l → Om l, (∀ a, y a ∈ Ks K (i - 1)) → ∑ a : Fin l, ζ ^ (a : ℕ) * y a = 0 → ∀ a, y a = 0 := by
  first | exact @GlobalTheory.Cyc.integers_eq_sum_zeta_pow | exact GlobalTheory.Cyc.integers_eq_sum_zeta_pow | (intros; apply GlobalTheory.Cyc.integers_eq_sum_zeta_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IrreducibleSpanAfterMapStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_span_after_map : ∀ {k Γ : Type} [Field k] [Group Γ] {L : Type} [Field L] (f : k →+* L) {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) (hW : Stable (matRep ((Units.coeHom _).comp ρ)) W), W ≠ ⊥ → Submodule.span k (Set.range fun g => (matRep ((Units.coeHom _).comp ρ) g).restrict (hW g)) = ⊤ → IsIrrSub (mapRep f ρ) (Submodule.span L ((fun v => f ∘ v) '' (W : Set (Fin a → k)))) := by
  first | exact @GlobalTheory.isIrrSub_mapRep_of_span_restrict_eq_top | exact GlobalTheory.isIrrSub_mapRep_of_span_restrict_eq_top | (intros; apply GlobalTheory.isIrrSub_mapRep_of_span_restrict_eq_top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsHausdorffInvariantsQuotientOfFiniteFreeStatement
section
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHausdorff_invariants_quotient_of_finiteFree : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.FiniteFree D → IsHausdorff (Ideal.span {(l : O)}) D.Z := by
  first | exact @GlobalTheory.InertiaEigenvalues.isHausdorff_Z_of_finiteFree | exact GlobalTheory.InertiaEigenvalues.isHausdorff_Z_of_finiteFree | (intros; apply GlobalTheory.InertiaEigenvalues.isHausdorff_Z_of_finiteFree <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KillsCokerAllOfKillsCokerPhiModuleLatticeStatement
section
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.killsCoker_all_of_killsCoker_phiModuleLattice : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (F : BKHom D₁ D₂), ∀ r : ℕ, GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.KillsCoker F.app (l ^ r) D₁.L D₂.L → GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.KillsAll F (l ^ r) := by
  first | exact @GlobalTheory.CokerLift.killsAll_of_killsCoker_L | exact GlobalTheory.CokerLift.killsAll_of_killsCoker_L | (intros; apply GlobalTheory.CokerLift.killsAll_of_killsCoker_L <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KirillovVanishingOfLimitStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kirillov_vanishing_of_limit : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) → ∀ Ψ, A.InI Ψ → (∀ a : A.K, IsUnit a → Tendsto (A.abelian₂ μK ψ a Ψ) (𝓝[≠] 0) (𝓝 0)) → (∀ z, Ψ (wS A.K * nS z) = 0) ∧ ∀ (a : A.K) (c : F), A.abelian₂ μK ψ a (fun h => Ψ (h * wS A.K)) c = 0 := by
  first | exact @GlobalTheory.JR.kirillov_vanishing_l2 | exact GlobalTheory.JR.kirillov_vanishing_l2 | (intros; apply GlobalTheory.JR.kirillov_vanishing_l2 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LagrangePrimePowMemIsotypicDegreePolySpanStatement
section
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lagrange_prime_pow_mem_isotypicDegreePoly_span : ∀ (l e a : ℕ) [Fact l.Prime], 1 ≤ a → e + 1 = l ^ a → ∀ (Sig : Finset (ZMod e)) (c : ZMod e) (A' N : ℕ), Sig.card ≤ N → 2 * A' + 2 < l → ∃ α β : Polynomial ℤ_[l], Polynomial.C ((l : ℤ_[l]) ^ GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho l Sig N) = α * (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.P₁ Sig c A').map (Int.castRingHom ℤ_[l]) + β * (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.P₂ Sig c A').map (Int.castRingHom ℤ_[l]) := by
  first | exact @GlobalTheory.lagrange_C_rho_eq_comb_degrees | exact GlobalTheory.lagrange_C_rho_eq_comb_degrees | (intros; apply GlobalTheory.lagrange_C_rho_eq_comb_degrees <;> assumption)
end


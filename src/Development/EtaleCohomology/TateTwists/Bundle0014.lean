import Development.EtaleCohomology.TateTwists.Bundle0007
import Development.EtaleCohomology.TateTwists.Bundle0011
import Development.EtaleCohomology.TateTwists.Bundle0006
import Development.EtaleCohomology.TateTwists.Bundle0003
import Development.EtaleCohomology.TateTwists.Bundle0009
import Development.EtaleCohomology.TateTwists.Bundle0012
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.EtaleCohomology.TateTwists.Bundle0010

-- bundled from Development.EtaleCohomology.TateTwists.EtaleFreePresheafMayerVietorisShortExactHolds
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.MvFree

theorem finsupp_mv {T α β γ M : Type*} [AddCommGroup M] (p1 : T → α) (p2 : T → β) (f : α → γ) (g : β → γ)
    (hf : Function.Injective f) (hg : Function.Injective g) (hc : ∀ t, f (p1 t) = g (p2 t))
    (hj : ∀ t t', p1 t = p1 t' ∧ p2 t = p2 t' → t = t')
    (hs : ∀ x y, f x = g y → ∃ t, p1 t = x ∧ p2 t = y) :
    Function.Injective (Finsupp.mapDomain (M := M) p1) ∧
    ∀ (p : α →₀ M) (q : β →₀ M), Finsupp.mapDomain f p + Finsupp.mapDomain g q = 0 →
      ∃ c : T →₀ M, Finsupp.mapDomain p1 c = p ∧ Finsupp.mapDomain p2 c = -q := by
  classical
  have hp1 : Function.Injective p1 := fun t t' h =>
    hj t t' ⟨h, hg (by rw [← hc, ← hc, h])⟩
  have hh : Function.Injective (f ∘ p1) := hf.comp hp1
  refine ⟨Finsupp.mapDomain_injective hp1, fun p q hpq => ?_⟩
  set z := Finsupp.mapDomain f p with hz
  have hz' : z = Finsupp.mapDomain g (-q) := by
    have h0 : Finsupp.mapDomain g q + Finsupp.mapDomain g (-q) = 0 := by
      rw [← Finsupp.mapDomain_add, add_neg_cancel, Finsupp.mapDomain_zero]
    rw [hz]; exact (eq_neg_of_add_eq_zero_left hpq).trans (eq_neg_of_add_eq_zero_right h0).symm
  have hsupp : (z.support : Set γ) ⊆ Set.range (f ∘ p1) := by
    intro x hx
    have h1 : x ∈ Set.range f := by
      have := Finsupp.mapDomain_support (f := f) (s := p) (by rw [← hz]; exact hx)
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 this; exact ⟨a, rfl⟩
    have h2 : x ∈ Set.range g := by
      rw [hz'] at hx
      have := Finsupp.mapDomain_support (f := g) (s := -q) hx
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 this; exact ⟨a, rfl⟩
    obtain ⟨a, rfl⟩ := h1
    obtain ⟨b, hb⟩ := h2
    obtain ⟨t, ht, -⟩ := hs a b hb.symm
    exact ⟨t, by simp [ht]⟩
  refine ⟨Finsupp.comapDomain (f ∘ p1) z hh.injOn, ?_, ?_⟩
  · apply Finsupp.mapDomain_injective hf
    rw [← Finsupp.mapDomain_comp, Finsupp.mapDomain_comapDomain _ hh _ hsupp]
  · apply Finsupp.mapDomain_injective hg
    have : g ∘ p2 = f ∘ p1 := funext fun t => (hc t).symm
    rw [← Finsupp.mapDomain_comp, this, Finsupp.mapDomain_comapDomain _ hh _ hsupp, hz']

theorem exact_of_eval {C D : Type*} [Category C] [Category D] [Abelian D]
    (S : ShortComplex (C ⥤ D)) (h : ∀ X, (S.map ((evaluation C D).obj X)).Exact) : S.Exact := by
  rw [ShortComplex.exact_iff_isZero_homology]
  apply Functor.isZero
  intro X
  exact ((ShortComplex.exact_iff_isZero_homology _).1 (h X)).of_iso (S.mapHomologyIso ((evaluation C D).obj X)).symm

end LateralTheory.EtaleFoundations.MvFree

namespace LateralTheory.EtaleFoundations.MvFree

noncomputable def mvIso {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D] (G : C ⥤ D) [G.Additive] {X1 A B X3 : C}
    (a : X1 ⟶ A) (b : X1 ⟶ B) (c : A ⟶ X3) (d : B ⟶ X3)
    (w : biprod.lift a (-b) ≫ biprod.desc c d = 0)
    (w' : biprod.lift (G.map a) (-G.map b) ≫ biprod.desc (G.map c) (G.map d) = 0) :
    (ShortComplex.mk _ _ w).map G ≅ ShortComplex.mk _ _ w' := by
  haveI := preservesBinaryBiproducts_of_preservesBiproducts G
  exact ShortComplex.isoMk (Iso.refl _) (G.mapBiprod A B) (Iso.refl _)
    (by show 𝟙 _ ≫ biprod.lift (G.map a) (-G.map b) = G.map (biprod.lift a (-b)) ≫ (G.mapBiprod A B).hom
        rw [biprod.map_lift_mapBiprod, Functor.map_neg, Category.id_comp])
    (by dsimp; rw [← biprod.mapBiprod_inv_map_desc]; erw [Iso.hom_inv_id_assoc]; simp; exact (Category.comp_id _).symm)

theorem mono_f_of_iso {C : Type*} [Category C] [HasZeroMorphisms C] {S T : ShortComplex C}
    (e : S ≅ T) [Mono S.f] : Mono T.f := by
  have h : T.f = e.inv.τ₁ ≫ S.f ≫ e.hom.τ₂ := by
    rw [← e.hom.comm₁₂, ← Category.assoc, ← ShortComplex.comp_τ₁, e.inv_hom_id, ShortComplex.id_τ₁,
      Category.id_comp]
  rw [h]; infer_instance

theorem biprod_ext_el {S : Type*} [Ring S] {A B : ModuleCat.{1} S} (z z' : ↑(A ⊞ B))
    (h1 : (biprod.fst : A ⊞ B ⟶ A) z = (biprod.fst : A ⊞ B ⟶ A) z')
    (h2 : (biprod.snd : A ⊞ B ⟶ B) z = (biprod.snd : A ⊞ B ⟶ B) z') :
    z = z' := by
  have e : ∀ w : ↑(A ⊞ B), (biprod.inl : A ⟶ A ⊞ B) ((biprod.fst : A ⊞ B ⟶ A) w) + (biprod.inr : B ⟶ A ⊞ B) ((biprod.snd : A ⊞ B ⟶ B) w) = w :=
    fun w => by
      have h := ConcreteCategory.congr_hom (biprod.total (X := A) (Y := B)) w
      rw [ConcreteCategory.id_apply] at h
      conv_rhs => rw [← h]
      rfl
  rw [← e z, ← e z', h1, h2]

theorem mc_exact {S : Type*} [Ring S] {X1 A B X3 : ModuleCat.{1} S} (u : X1 ⟶ A) (v : X1 ⟶ B)
    (c : A ⟶ X3) (d : B ⟶ X3) (w : biprod.lift u (-v) ≫ biprod.desc c d = 0)
    (hu : Function.Injective u)
    (hex : ∀ p q, c p + d q = 0 → ∃ x, u x = p ∧ v x = -q) :
    Mono (biprod.lift u (-v)) ∧ (ShortComplex.mk (biprod.lift u (-v)) (biprod.desc c d) w).Exact := by
  constructor
  · have : Mono u := (ModuleCat.mono_iff_injective u).2 hu
    have : Mono (biprod.lift u (-v) ≫ biprod.fst) := by rw [biprod.lift_fst]; infer_instance
    exact mono_of_mono _ biprod.fst
  · rw [ShortComplex.moduleCat_exact_iff]
    intro x2 hx2
    have hx2' : c ((biprod.fst : A ⊞ B ⟶ A) x2) + d ((biprod.snd : A ⊞ B ⟶ B) x2) = 0 := by
      have h : (biprod.desc c d : A ⊞ B ⟶ X3) x2 = 0 := hx2
      rw [biprod.desc_eq] at h
      simpa using h
    obtain ⟨x, h1, h2⟩ := hex _ _ hx2'
    refine ⟨x, ?_⟩
    apply biprod_ext_el
    · dsimp; rw [← ConcreteCategory.comp_apply, biprod.lift_fst, h1]
    · dsimp; rw [← ConcreteCategory.comp_apply, biprod.lift_snd]
      simp [h2]

theorem pointwise (R : Type) [CommRing R] {P Q E : PSh} (f : P ⟶ E) (g : Q ⟶ E) [Mono f] [Mono g]
    (X : Scheme.{0}ᵒᵖ) (w) :
    Mono (biprod.lift (((freeP R).map (pullback.fst f g)).app X) (-((freeP R).map (pullback.snd f g)).app X)) ∧
    (ShortComplex.mk (biprod.lift (((freeP R).map (pullback.fst f g)).app X) (-((freeP R).map (pullback.snd f g)).app X))
      (biprod.desc (((freeP R).map f).app X) (((freeP R).map g).app X)) w).Exact := by
  have hpb := (IsPullback.of_hasPullback f g).map ((evaluation _ _).obj X)
  rw [Types.isPullback_iff] at hpb
  obtain ⟨hw, hj, hs⟩ := hpb
  dsimp at hw hj hs
  have hf : Function.Injective (f.app X) := (mono_iff_injective (f.app X)).1 inferInstance
  have hg : Function.Injective (g.app X) := (mono_iff_injective (g.app X)).1 inferInstance
  obtain ⟨hinj, hex⟩ := finsupp_mv (M := ULift.{1} R)
    (fun y : ULift.{1} ((pullback f g).obj X) => ULift.up ((pullback.fst f g).app X y.down))
    (fun y : ULift.{1} ((pullback f g).obj X) => ULift.up ((pullback.snd f g).app X y.down))
    (fun y : ULift.{1} (P.obj X) => ULift.up (f.app X y.down))
    (fun y : ULift.{1} (Q.obj X) => ULift.up (g.app X y.down))
    (fun x y h => ULift.ext _ _ (hf (congrArg ULift.down h)))
    (fun x y h => ULift.ext _ _ (hg (congrArg ULift.down h)))
    (fun t => congrArg ULift.up (by simpa using ConcreteCategory.congr_hom hw t.down))
    (fun t t' h => ULift.ext _ _ (hj _ _ ⟨congrArg ULift.down h.1, congrArg ULift.down h.2⟩))
    (fun x y h => by
      obtain ⟨t, h1, h2⟩ := hs x.down y.down (congrArg ULift.down h)
      exact ⟨ULift.up t, congrArg ULift.up h1, congrArg ULift.up h2⟩)
  exact mc_exact _ _ _ _ w hinj (fun p q h => hex p q h)

end LateralTheory.EtaleFoundations.MvFree

namespace LateralTheory.EtaleFoundations

open MvFree in
theorem etale_free_presheaf_mayer_vietoris_short_exact_holds : EtaleFreePresheafMayerVietorisShortExact := by
  intro R _ P Q E f g _ _
  have w0 : biprod.lift ((freeP R).map (pullback.fst f g)) (-(freeP R).map (pullback.snd f g)) ≫
      biprod.desc ((freeP R).map f) ((freeP R).map g) = 0 := by
    rw [biprod.lift_desc, Preadditive.neg_comp, ← Functor.map_comp, ← Functor.map_comp,
      pullback.condition, add_neg_cancel]
  let S := ShortComplex.mk _ _ w0
  have hev : ∀ X, Mono ((S.map ((evaluation _ _).obj X)).f) ∧ (S.map ((evaluation _ _).obj X)).Exact := by
    intro X
    have w1 : biprod.lift (((freeP R).map (pullback.fst f g)).app X) (-((freeP R).map (pullback.snd f g)).app X) ≫
        biprod.desc (((freeP R).map f).app X) (((freeP R).map g).app X) = 0 := by
      rw [biprod.lift_desc, Preadditive.neg_comp, ← NatTrans.comp_app, ← NatTrans.comp_app,
        ← Functor.map_comp, ← Functor.map_comp, pullback.condition, add_neg_cancel]
    obtain ⟨hm, hx⟩ := pointwise R f g X w1
    let e := mvIso ((evaluation _ _).obj X) _ _ _ _ w0 w1
    exact ⟨@mono_f_of_iso _ _ _ _ _ e.symm hm, ShortComplex.exact_of_iso e.symm hx⟩
  have hSm : Mono S.f := by
    have : ∀ X, Mono (S.f.app X) := fun X => (hev X).1
    exact NatTrans.mono_of_mono_app _
  have hSe : S.Exact := exact_of_eval S (fun X => (hev X).2)
  let G := presheafToSheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))
  have w2 : biprod.lift (G.map ((freeP R).map (pullback.fst f g))) (-G.map ((freeP R).map (pullback.snd f g))) ≫
      biprod.desc (G.map ((freeP R).map f)) (G.map ((freeP R).map g)) = 0 := by
    rw [biprod.lift_desc, Preadditive.neg_comp, ← Functor.map_comp, ← Functor.map_comp,
      ← Functor.map_comp, ← Functor.map_comp, pullback.condition, add_neg_cancel]
  let e := mvIso G _ _ _ _ w0 w2
  have hGm : Mono ((S.map G).f) := (inferInstance : Mono (G.map S.f))
  exact ⟨mono_f_of_iso e, w2, ShortComplex.exact_of_iso e (hSe.map G)⟩

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleInjectiveResolutionDegreeZeroInjective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
namespace LateralTheory.EtaleFoundations

theorem etale_injective_resolution_degree_zero_injective (q : ℕ) (F : Shv (ZMod q)) : Injective ((res _ F).X 0) := by
  unfold res
  exact inferInstance

theorem etale_twist_extends_through_mono_to_resolution_holds : EtaleTwistExtendsThroughMonoToResolutionZero := by
  intro q _ M j hj
  have := etale_injective_resolution_degree_zero_injective q (tw q 1)
  exact ⟨Injective.factorThru (resι _ (tw q 1)) j, Injective.comp_factorThru _ _⟩

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleKInjectiveHomLiftAlongQuasiIsoHolds
section
open CategoryTheory Limits GlobalTheory.EtC

theorem LateralTheory.EtaleFoundations.etale_kInjective_hom_lift_along_quasiIso_holds : LateralTheory.EtaleFoundations.EtaleKInjectiveHomLiftAlongQuasiIsoUpToHomotopy := by
  intro R _ K L I _ f _
  have hI := CochainComplex.IsKInjective.rightOrthogonal I
  rw [← ObjectProperty.isLocal_trW] at hI
  have hf : (HomotopyCategory.subcategoryAcyclic (Shv R)).trW
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map f) := by
    rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic,
      HomotopyCategory.quotient_map_mem_quasiIso_iff]
    exact (HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance
  have hb := hI _ hf
  refine ⟨fun a => ?_, fun m m' h => ?_⟩
  · obtain ⟨m', hm'⟩ := hb.2 ((HomotopyCategory.quotient _ _).map a)
    obtain ⟨m, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective m'
    refine ⟨m, ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
    rw [Functor.map_comp]; exact hm'
  · obtain ⟨h⟩ := h
    have e := HomotopyCategory.eq_of_homotopy _ _ h
    rw [Functor.map_comp, Functor.map_comp] at e
    exact ⟨HomotopyCategory.homotopyOfEq _ _ (hb.1 e)⟩
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleLocallyExistsPrimitiveRootOfUnityOfInvertib
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.PrimLocPf

theorem ring_core {R K : Type} [CommRing R] [Field K] (φ : R →+* K) (q : ℕ) [NeZero q]
    (hq : IsUnit (q : R)) (ζ x : R) (hζ : Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0)
    (hx : x ^ q = 1) :
    ∃ n < q, ∃ s : R, φ s ≠ 0 ∧ s * (x - ζ ^ n) = 0 ∧ IsPrimitiveRoot (φ ζ) q := by
  have hqK : (q : K) ≠ 0 := by
    have := hq.map φ; simpa using this.ne_zero
  have : NeZero (q : K) := ⟨hqK⟩
  have hζK : IsPrimitiveRoot (φ ζ) q := by
    rw [← Polynomial.isRoot_cyclotomic_iff]
    have h := Polynomial.aeval_algHom_apply φ.toIntAlgHom ζ (Polynomial.cyclotomic q ℤ)
    rw [hζ, map_zero] at h
    simpa [Polynomial.IsRoot, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
      Polynomial.map_cyclotomic] using h
  have hζq : ζ ^ q = 1 := by
    obtain ⟨c, hc⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
    have h := congrArg (Polynomial.aeval ζ) hc
    simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, map_mul, hζ, zero_mul] at h
    exact sub_eq_zero.mp h
  have hxK : (φ x) ^ q = 1 := by rw [← map_pow, hx, map_one]
  obtain ⟨n, hn, hnx⟩ := hζK.eq_pow_of_pow_eq_one hxK
  set t := x * ζ ^ (q - n) with ht
  refine ⟨n, hn, ∑ i ∈ Finset.range q, t ^ i, ?_, ?_, hζK⟩
  · have h1 : φ t = 1 := by
      rw [ht, map_mul, map_pow, ← hnx, ← pow_add, Nat.add_sub_cancel' hn.le, hζK.pow_eq_one]
    simp [map_sum, map_pow, h1, hqK]
  · have hg : (∑ i ∈ Finset.range q, t ^ i) * (t - 1) = 0 := by
      rw [geom_sum_mul, ht, mul_pow, hx, ← pow_mul, mul_comm (q - n) q, pow_mul, hζq, one_pow,
        one_mul, sub_self]
    have : x - ζ ^ n = (t - 1) * ζ ^ n := by
      rw [ht, sub_mul, mul_assoc, ← pow_add, Nat.sub_add_cancel hn.le, hζq, mul_one, one_mul]
    rw [this, ← mul_assoc, hg, zero_mul]

theorem isUnit_of_basicOpen_top (X : Scheme.{0}) (f : Γ(X, ⊤)) (h : X.basicOpen f = ⊤) :
    IsUnit f := by
  have key : ∀ (O : X.Opens) (_ : O = ⊤) (hle : O ≤ ⊤),
      IsUnit (X.presheaf.map (homOfLE hle).op f) → IsUnit f := by
    intro O hO; subst hO; intro hle hu; simpa using hu
  exact key _ h (X.basicOpen_le f) (X.toRingedSpace.isUnit_res_basicOpen f)

theorem affine_nbhd (U : Scheme.{0}) (s : Γ(U, ⊤)) (y : U) (hy : y ∈ U.basicOpen s) :
    ∃ (V : Scheme.{0}) (g : V ⟶ U), IsAffine V ∧ Etale g ∧ y ∈ Set.range g ∧
      IsUnit (g.appTop.hom s) := by
  obtain ⟨W, hWa, hyW, hW⟩ : ∃ W : U.Opens, IsAffineOpen W ∧ y ∈ W ∧ W ≤ U.basicOpen s :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp U.isBasis_affineOpens) hy
  refine ⟨W, Scheme.Opens.ι W, hWa, inferInstance, by simpa using hyW, ?_⟩
  apply isUnit_of_basicOpen_top
  rw [← Scheme.preimage_basicOpen_top]
  ext z
  simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
  exact hW (by have h := Set.mem_range_self (f := W.ι) z; simpa using h)

theorem cyc_pow_eq_one {R : Type} [CommRing R] (q : ℕ) (ζ : R)
    (hζ : Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0) : ζ ^ q = 1 := by
  obtain ⟨c, hc⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
  have h := congrArg (Polynomial.aeval ζ) hc
  simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, map_mul, hζ, zero_mul] at h
  exact sub_eq_zero.mp h

theorem mono_pow {U : Scheme.{0}} (x ζ : Γ(U, ⊤)) : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V),
    (∃ a : ℕ, g.appTop.hom x = g.appTop.hom ζ ^ a) →
    ∃ a : ℕ, (k ≫ g).appTop.hom x = (k ≫ g).appTop.hom ζ ^ a := by
  rintro V W g k ⟨a, ha⟩
  refine ⟨a, ?_⟩
  show k.appTop.hom (g.appTop.hom x) = (k.appTop.hom (g.appTop.hom ζ)) ^ a
  rw [ha, map_pow]

theorem part3 (q : ℕ) [NeZero q] (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (x : Γ(U, ⊤))
    (hx : x ^ q = 1) : Loc U fun _ g => ∃ a : ℕ, g.appTop.hom x = g.appTop.hom ζ.1 ^ a := by
  rw [etale_sheaf_section_locally_iff_of_presheaf_facts U _ (mono_pow x ζ.1)]
  intro y
  obtain ⟨n, -, s, hs, hsx, -⟩ := ring_core (U.Γevaluation y).hom q ζ.2.1 ζ.1 x ζ.2.2 hx
  have hy : y ∈ U.basicOpen s := (U.evaluation_ne_zero_iff_mem_basicOpen (U := ⊤) y trivial s).mp hs
  obtain ⟨V, g, hV, hg, hyr, hu⟩ := affine_nbhd U s y hy
  refine ⟨V, g, hV, hg, hyr, n, ?_⟩
  have h := congrArg g.appTop.hom hsx
  rw [map_mul, map_sub, map_pow, map_zero] at h
  exact sub_eq_zero.mp (hu.mul_right_eq_zero.mp h)

theorem mono_unit {q : ℕ} {U : Scheme.{0}} (x ζ : Γ(U, ⊤)) :
    ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V),
    (∃ a : (ZMod q)ˣ, g.appTop.hom x = g.appTop.hom ζ ^ (a : ZMod q).val) →
    ∃ a : (ZMod q)ˣ, (k ≫ g).appTop.hom x = (k ≫ g).appTop.hom ζ ^ (a : ZMod q).val := by
  rintro V W g k ⟨a, ha⟩
  refine ⟨a, ?_⟩
  show k.appTop.hom (g.appTop.hom x) = (k.appTop.hom (g.appTop.hom ζ)) ^ (a : ZMod q).val
  rw [ha, map_pow]

theorem part2 (q : ℕ) [NeZero q] (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) :
    Loc U fun _ g => ∃ a : (ZMod q)ˣ, g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val := by
  rw [etale_sheaf_section_locally_iff_of_presheaf_facts U _ (mono_unit ξ.1 ζ.1)]
  intro y
  obtain ⟨n, hn, s, hs, hsx, hζK⟩ := ring_core (U.Γevaluation y).hom q ζ.2.1 ζ.1 ξ.1 ζ.2.2
    (cyc_pow_eq_one q ξ.1 ξ.2.2)
  obtain ⟨-, -, -, -, -, hξK⟩ := ring_core (U.Γevaluation y).hom q ξ.2.1 ξ.1 ξ.1 ξ.2.2
    (cyc_pow_eq_one q ξ.1 ξ.2.2)
  have hφ : (U.Γevaluation y).hom ξ.1 = (U.Γevaluation y).hom ζ.1 ^ n := by
    have h := congrArg (U.Γevaluation y).hom hsx
    rw [map_mul, map_sub, map_pow, map_zero] at h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hs)
  have hcop : n.Coprime q := (hζK.pow_iff_coprime (Nat.pos_of_neZero q) n).mp (hφ ▸ hξK)
  have hy : y ∈ U.basicOpen s :=
    (U.evaluation_ne_zero_iff_mem_basicOpen (U := ⊤) y trivial s).mp hs
  obtain ⟨V, g, hV, hg, hyr, hu⟩ := affine_nbhd U s y hy
  refine ⟨V, g, hV, hg, hyr, ZMod.unitOfCoprime n hcop, ?_⟩
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hn]
  have h := congrArg g.appTop.hom hsx
  rw [map_mul, map_sub, map_pow, map_zero] at h
  exact sub_eq_zero.mp (hu.mul_right_eq_zero.mp h)

end LateralTheory.EtaleFoundations.PrimLocPf

namespace LateralTheory.EtaleFoundations

def EtaleLocallyExistsPrimitiveRootOfUnityOfInvertibleOrder : Prop :=
  ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) →
    Loc U fun V _ => Nonempty (Prim q Γ(V, ⊤))

def EtaleLocallyKummerRootsOfUnits : Prop :=
  ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ,
    Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u

theorem etale_locally_roots_of_unity_structure_of_exists_and_kummer (h1 : EtaleLocallyExistsPrimitiveRootOfUnityOfInvertibleOrder) (h4 : EtaleLocallyKummerRootsOfUnits) :
    EtalePrimitiveRootsExistLocally := by
  intro q _ U
  exact ⟨h1 q U, PrimLocPf.part2 q U, fun ζ x hx => PrimLocPf.part3 q U ζ x hx,
    fun hq u => h4 q U hq u⟩

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleLocallyExistsQthRootOfUnitWhenQInvertible
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.FirstChernUniqueness

lemma sec_sub {q : ℕ} {F : Shv (ZMod q)} (hF : IsZero F) (U : Scheme.{0}) (a b : Sec F U) : a = b := by
  have h1 : IsZero F.obj := (sheafToPresheaf _ _).map_isZero hF
  have h2 : IsZero (F.obj.obj (op U)) := h1.obj (op U)
  have := (ModuleCat.isZero_iff_subsingleton.mp h2)
  exact Subsingleton.elim _ _

lemma res_zero_neg (q : ℕ) (s : ℤ) (hs : s < 0) : IsZero ((res _ (tw q 1)).X s) := by
  unfold res
  exact CochainComplex.isZero_of_isStrictlyGE _ 0 _ (by omega)

lemma sub_res {E : Spc} {N : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) :
    (x.res g).sub j l h = (x.sub j l h).res g := by
  unfold Sx.sub Sx.res
  exact (NatTrans.naturality_apply (E.map (SimplexCategory.subinterval j l h).op) g.op x)

def ev_basic : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}, (∀ (α β : Cochain ((chains R).obj E) I n) p s h U x, ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x ∧ ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x ∧ ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 ∧ ∀ c : ℤ, ev (c • α) p s h U x = c • ev α p s h U x) ∧ (∀ (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (ev α p s h U x) = ev α p s h V (x.res g)) ∧ (∀ α β : Cochain ((chains R).obj E) I n, (∀ p s h U x, ev α p s h U x = ev β p s h U x) → α = β) ∧ (∀ {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U), ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U (x.map f)) ∧ ∀ {J : Cx R} (m : I ⟶ J) (α : Cochain ((chains R).obj E) I n) p s h U x, ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x)

def sec_glue : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}), (∀ a b : Sec F U, (Loc U fun _ g => Sec.res g a = Sec.res g b) → a = b) ∧ ∀ (S : Sieve U), S ∈ Scheme.etaleTopology U → ∀ s : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec F V, (∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : S.arrows g), Sec.res k (s V g hg) = s W (k ≫ g) (S.downward_closed hg k)) → ∃ a : Sec F U, ∀ V g hg, Sec.res g a = s V g hg

lemma loc_imp {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P)
    (h : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hSP⟩ := hP
  exact ⟨S, hS, fun V g hg => h V g (hSP V g hg)⟩

def EtaleLocallyExistsQthRootOfUnitWhenQInvertible : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ,
  Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u

lemma glMat_res {V U : Scheme.{0}} (g : V ⟶ U) (y : Sx (ofCat (glCat 1)) 1 U) :
    (glMat (y.res g) : Matrix (Fin 1) (Fin 1) Γ(V, ⊤)) = g.appTop.hom.mapMatrix (glMat y : Matrix (Fin 1) (Fin 1) Γ(U, ⊤)) := by
  rfl

lemma lineUnit_res {E : Spc} (L : E ⟶ ofCat (glCat 1)) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E 1 U) :
    lineUnit L (x.res g) = Units.map g.appTop.hom.toMonoidHom (lineUnit L x) := by
  unfold lineUnit
  have hn : (L.app (op (SimplexCategory.mk 1))).app (op V) (x.res g) =
      Sx.res g ((L.app (op (SimplexCategory.mk 1))).app (op U) x) := by
    unfold Sx.res; rw [NatTrans.naturality_apply]
  rw [hn]
  ext
  simp only [Units.coe_map, Matrix.GeneralLinearGroup.val_det_apply, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  rw [glMat_res, RingHom.map_det]

lemma root_line (hr : EtaleLocallyExistsQthRootOfUnitWhenQInvertible) (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hi : Inv q E)
    (U : Scheme.{0}) (x : Sx E 1 U) : Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = lineUnit L (x.res g) := by
  refine loc_imp (hr q U (hi U ⟨x.sub 0 0 (by omega)⟩) (lineUnit L x)) fun V g hv => ?_
  obtain ⟨v, hv⟩ := hv
  exact ⟨v, by rw [lineUnit_res]; exact hv⟩

lemma loc_and {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P) (hQ : Loc U Q) :
    Loc U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, hSP⟩ := hP
  obtain ⟨T, hT, hTQ⟩ := hQ
  exact ⟨S ⊓ T, Scheme.etaleTopology.intersection_covering hS hT, fun V g hg => ⟨hSP V g hg.1, hTQ V g hg.2⟩⟩

end LateralTheory.EtaleFoundations.FirstChernUniqueness
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleSectionsGlueOverCoverOfComponents
section
namespace LateralTheory.Fin.EtaleSheafSectionsSeparatedAndGlue
theorem etale_sections_glue_over_cover_of_components : LateralTheory.EtaleFoundations.EtaleSheafSectionsSeparatedAndGlue := by
  apply LateralTheory.EtaleFoundations.etale_sheaf_sections_glue_of_forget_isSheaf
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleSheafSectionsSeparatedAndGlue := etale_sections_glue_over_cover_of_components
end LateralTheory.Fin.EtaleSheafSectionsSeparatedAndGlue
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleSemilinearCohomologyOperationImageSpecOfHyp
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem etale_semilinear_cohomology_operation_image_spec_of_hyp
    (hImage₂ : ∀ (S R : Type) [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J),
      (∀ (E : Spc) (n : ℤ) (α : Cocycle ((chains S).obj E) I n), ∃ β : Cocycle ((chains R).obj E) J n, ρ.IsImage α.1 β.1) ∧
      ∀ (E : Spc) (n : ℤ) (α : Cocycle ((chains S).obj E) I n) (β : Cocycle ((chains R).obj E) J n),
        ρ.IsImage α.1 β.1 → ρ.op.app E n (CohomologyClass.mk α) = CohomologyClass.mk β) :
    EtaleSemilinearCohomologyOperationImageSpec :=
  hImage₂

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleSheafLocalizationPropertiesOfComponents
section
namespace LateralTheory.Fin.EtaleSheafificationSectionsLocallyFromPresheaf
theorem etale_sheaf_localization_properties_of_components : LateralTheory.EtaleFoundations.EtaleSheafificationSectionsLocallyFromPresheaf := by
  apply LateralTheory.EtaleFoundations.ShfLocPf.etale_sheaf_sections_eq_of_locally_eq
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleSheafificationSectionsLocallyFromPresheaf := etale_sheaf_localization_properties_of_components
end LateralTheory.Fin.EtaleSheafificationSectionsLocallyFromPresheaf
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleSingleSheafHomotopicMapsEqualHolds
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem LateralTheory.EtaleFoundations.etale_single_sheaf_homotopic_maps_equal_holds : LateralTheory.EtaleFoundations.EtaleSingleSheafHomotopicMapsToNonnegComplexEqual := by
  intro R _ F I _ a b ⟨h⟩
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : i = 0
  · subst hi
    rw [h.comm 0]
    have h1 : dNext 0 h.hom = 0 := by
      rw [dNext_eq h.hom (show (ComplexShape.up ℤ).Rel 0 1 by simp)]
      rw [show (sgl F).d 0 1 = 0 from
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F 1 (by omega)).eq_of_tgt _ _]
      simp
    have h2 : prevD 0 h.hom = 0 := by
      rw [prevD_eq h.hom (show (ComplexShape.up ℤ).Rel (-1) 0 by simp)]
      rw [show h.hom 0 (-1) = 0 from (CochainComplex.isZero_of_isStrictlyGE I 0 (-1) (by omega)).eq_of_tgt _ _]
      simp
    rw [h1, h2]; simp
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F i hi).eq_of_src _ _
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleTateTwistGeneratorMapIsIsoOfInjSurj
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

def LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorMapLocallySurjective : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j k : ℤ) (T : Shv (ZMod q)) (μ : Pair (sgl (tw q i)) (sgl (tw q j)) (sgl T)),
    μ.IsTensor → i + j = k → ∀ φ : tw q k ⟶ T, (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)),
      Sec.map (sglι T) (Sec.map φ (twGen k ζ)) =
        μ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ))) →
    ∀ (U : Scheme.{0}) (b : Sec T U), Loc U fun V g => ∃ a : Sec (tw q k) V, Sec.map φ a = Sec.res g b

def LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorMapSectionsInjective : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j k : ℤ) (T : Shv (ZMod q)) (μ : Pair (sgl (tw q i)) (sgl (tw q j)) (sgl T)),
    μ.IsTensor → i + j = k → ∀ φ : tw q k ⟶ T, (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)),
      Sec.map (sglι T) (Sec.map φ (twGen k ζ)) =
        μ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ))) →
    ∀ (U : Scheme.{0}) (a : Sec (tw q k) U), Sec.map φ a = 0 → Loc U fun _ g => Sec.res g a = 0

theorem LateralTheory.EtaleFoundations.etale_tate_twist_generator_map_isIso_of_inj_surj (hme : LateralTheory.EtaleFoundations.EtaleSheafMonoEpiSectionCriteria)
    (hs : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorMapLocallySurjective) (hi : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorMapSectionsInjective) :
    LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorCompatibleMapIsIso := by
  intro q _ i j k T μ hμ hk φ hφ
  have h := hme (ZMod q) φ
  have hm : Mono φ := h.2.1.2 (hi q i j k T μ hμ hk φ hφ)
  have he : Epi φ := h.2.2.1.2 (hs q i j k T μ hμ hk φ hφ)
  exact isIso_of_mono_of_epi φ
end
end


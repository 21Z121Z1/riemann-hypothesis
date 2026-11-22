import Mathlib

-- bundled from GroundTheory.ProfiniteCohomology.AdditiveHilbert
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory CategoryTheory.Limits

universe u

section NormalBasis

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

theorem normalBasis_repr_apply_smul (σ τ : Gal(L/K)) (y : L) :
    (IsGalois.normalBasis K L).repr (σ y) τ = (IsGalois.normalBasis K L).repr y (σ⁻¹ * τ) := by
  have hb (ρ : Gal(L/K)) :
      σ (IsGalois.normalBasis K L ρ) = IsGalois.normalBasis K L (σ * ρ) := by
    rw [IsGalois.normalBasis_apply (σ * ρ), IsGalois.normalBasis_apply ρ, AlgEquiv.mul_apply]
  have key : (Finsupp.lapply τ ∘ₗ (IsGalois.normalBasis K L).repr.toLinearMap ∘ₗ σ.toLinearMap :
      L →ₗ[K] K) = Finsupp.lapply (σ⁻¹ * τ) ∘ₗ (IsGalois.normalBasis K L).repr.toLinearMap := by
    refine (IsGalois.normalBasis K L).ext fun ρ => ?_
    change (IsGalois.normalBasis K L).repr (σ (IsGalois.normalBasis K L ρ)) τ =
      (IsGalois.normalBasis K L).repr (IsGalois.normalBasis K L ρ) (σ⁻¹ * τ)
    classical
    rw [hb, Module.Basis.repr_self, Module.Basis.repr_self]
    simp only [Finsupp.single_apply, eq_inv_mul_iff_mul_eq]
  exact LinearMap.congr_fun key y

end NormalBasis

section Coinduced

variable (k : Type u) (K L : Type u) [CommRing k] [Field K] [Field L] [Algebra K L]
  [Algebra k K] [Algebra k L] [IsScalarTower k K L] [FiniteDimensional K L] [IsGalois K L]

noncomputable def galoisCoindIso :
    Rep.ofDistribMulAction k Gal(L/K) L ≅
      Rep.coind (⊥ : Subgroup Gal(L/K)).subtype (Rep.trivial k (⊥ : Subgroup Gal(L/K)) K) := by
  have htop : (Representation.trivial k (⊥ : Subgroup Gal(L/K)) K).coindV
      (⊥ : Subgroup Gal(L/K)).subtype = ⊤ := by
    ext f
    simp only [Representation.mem_coindV, Submodule.mem_top, iff_true]
    rintro ⟨g, hg⟩ h
    rw [Subgroup.mem_bot] at hg
    subst hg
    simp
  let e : L ≃ₗ[k] _ :=
    ((IsGalois.normalBasis K L).equivFun.restrictScalars k).trans
      ((LinearEquiv.funCongrLeft k K (Equiv.inv Gal(L/K))).trans (LinearEquiv.ofTop _ htop).symm)
  refine Rep.mkIso (Representation.Equiv.mk e fun σ => ?_)
  refine LinearMap.ext fun y => Subtype.ext (funext fun h => ?_)
  change (IsGalois.normalBasis K L).repr (σ y) h⁻¹ =
    (IsGalois.normalBasis K L).repr y (h * σ)⁻¹
  rw [normalBasis_repr_apply_smul, mul_inv_rev]

end Coinduced

section Vanishing

open groupCohomology

variable (k : Type u) (K L : Type u) [CommRing k] [Field K] [Field L] [Algebra K L]
  [Algebra k K] [Algebra k L] [IsScalarTower k K L] [FiniteDimensional K L] [IsGalois K L]

theorem isZero_groupCohomology_succ (n : ℕ) :
    IsZero (groupCohomology (Rep.ofDistribMulAction k Gal(L/K) L) (n + 1)) :=
  (isZero_groupCohomology_succ_of_subsingleton
      (Rep.trivial k (⊥ : Subgroup Gal(L/K)) K) n).of_iso
    ((groupCohomology.functor k Gal(L/K) (n + 1)).mapIso (galoisCoindIso k K L) ≪≫
      groupCohomology.coindIso _ (n + 1))

theorem isZero_groupCohomology {n : ℕ} (hn : n ≠ 0) :
    IsZero (groupCohomology (Rep.ofDistribMulAction k Gal(L/K) L) n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact isZero_groupCohomology_succ k K L m

theorem isZero_groupCohomology_galois {n : ℕ} (hn : n ≠ 0) :
    IsZero (groupCohomology (Rep.ofDistribMulAction K Gal(L/K) L) n) :=
  isZero_groupCohomology K K L hn

theorem subsingleton_groupCohomology_galois {n : ℕ} (hn : n ≠ 0) :
    Subsingleton (groupCohomology (Rep.ofDistribMulAction K Gal(L/K) L) n) :=
  ModuleCat.subsingleton_of_isZero (isZero_groupCohomology_galois K L hn)

theorem isCoboundary₁_of_isCocycle₁_galois (f : Gal(L/K) → L) (hf : IsCocycle₁ f) :
    IsCoboundary₁ f := by
  have := subsingleton_groupCohomology_galois K L one_ne_zero
  have h0 : H1π (Rep.ofDistribMulAction K Gal(L/K) L) (cocyclesOfIsCocycle₁ hf) = 0 :=
    Subsingleton.elim _ _
  rw [H1π_eq_zero_iff] at h0
  exact isCoboundary₁_of_mem_coboundaries₁ f h0

end Vanishing

section Integral

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

end Integral

end GroundTheory.ProfCoh
end

-- bundled from GroundTheory.ProfiniteCohomology.BridgeNested
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory TopRep ContRepresentation

universe u v w

section Cons

variable {G : Type v} [TopologicalSpace G]

def finConsHomeomorph (m : ℕ) : G × (Fin m → G) ≃ₜ (Fin (m + 1) → G) where
  toFun p := Fin.cons p.1 p.2
  invFun x := (x 0, Fin.tail x)
  left_inv p := by simp
  right_inv x := by simp
  continuous_toFun := Continuous.finCons (A := fun _ : Fin (m + 1) => G) continuous_fst continuous_snd
  continuous_invFun := (continuous_apply 0).prodMk (continuous_pi fun _ => continuous_apply _)

@[simp]
theorem finConsHomeomorph_symm_apply (m : ℕ) (x : Fin (m + 1) → G) :
    (finConsHomeomorph m).symm x = (x 0, Fin.tail x) :=
  rfl

end Cons

variable {k G : Type u} [Ring k] [TopologicalSpace k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G]

def nestedHomeomorph (X : TopRep.{u} k G) : (m : ℕ) → resolutionX X m ≃ₜ C(Fin m → G, X)
  | 0 => Homeomorph.continuousMapOfUnique
  | m + 1 => ((Homeomorph.refl G).arrowCongr (nestedHomeomorph X m)).trans
      (Homeomorph.curry.symm.trans ((finConsHomeomorph m).arrowCongr (Homeomorph.refl X)))

variable (X : TopRep.{u} k G)

@[simp]
theorem nestedHomeomorph_zero_apply (v : resolutionX X 0) (x : Fin 0 → G) :
    nestedHomeomorph X 0 v x = v :=
  rfl

theorem nestedHomeomorph_succ_apply (m : ℕ) (f : resolutionX X (m + 1))
    (x : Fin (m + 1) → G) :
    nestedHomeomorph X (m + 1) f x =
      nestedHomeomorph X m ((f : C(G, resolutionX X m)) (x 0)) (Fin.tail x) :=
  rfl

theorem nestedHomeomorph_add (m : ℕ) (a b : resolutionX X m) :
    nestedHomeomorph X m (a + b) = nestedHomeomorph X m a + nestedHomeomorph X m b := by
  induction m with
  | zero => ext x; rfl
  | succ m ih =>
    ext x
    change nestedHomeomorph X m (((a + b : resolutionX X (m + 1)) : C(G, resolutionX X m)) (x 0))
        (Fin.tail x) = nestedHomeomorph X m ((a : C(G, resolutionX X m)) (x 0)) (Fin.tail x) +
          nestedHomeomorph X m ((b : C(G, resolutionX X m)) (x 0)) (Fin.tail x)
    rw [ContinuousMap.add_apply, ih]
    rfl

theorem nestedHomeomorph_smul (m : ℕ) (r : k) (a : resolutionX X m) :
    nestedHomeomorph X m (r • a) = r • nestedHomeomorph X m a := by
  induction m with
  | zero => ext x; rfl
  | succ m ih =>
    ext x
    change nestedHomeomorph X m (((r • a : resolutionX X (m + 1)) : C(G, resolutionX X m)) (x 0))
        (Fin.tail x) = r • nestedHomeomorph X m ((a : C(G, resolutionX X m)) (x 0)) (Fin.tail x)
    rw [ContinuousMap.smul_apply, ih]
    rfl

def nestedLinearEquiv (m : ℕ) : resolutionX X m ≃ₗ[k] C(Fin m → G, X) where
  toFun := nestedHomeomorph X m
  invFun := (nestedHomeomorph X m).symm
  map_add' := nestedHomeomorph_add X m
  map_smul' := nestedHomeomorph_smul X m
  left_inv := (nestedHomeomorph X m).symm_apply_apply
  right_inv := (nestedHomeomorph X m).apply_symm_apply

@[simp]
theorem nestedLinearEquiv_apply (m : ℕ) (a : resolutionX X m) :
    nestedLinearEquiv X m a = nestedHomeomorph X m a :=
  rfl

theorem nestedHomeomorph_ρ_apply (m : ℕ) (g : G) (a : resolutionX X m) (x : Fin m → G) :
    nestedHomeomorph X m ((resolutionX X m).ρ g a) x =
      X.ρ g (nestedHomeomorph X m a fun i => g⁻¹ * x i) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [nestedHomeomorph_succ_apply, nestedHomeomorph_succ_apply]
    exact ih _ _

theorem nestedHomeomorph_d_apply (m : ℕ) (a : resolutionX X m) (x : Fin (m + 1) → G) :
    nestedHomeomorph X (m + 1) ((d X m).hom a) x =
      ∑ i : Fin (m + 1), (-1 : k) ^ (i : ℕ) • nestedHomeomorph X m a (fun j => x (i.succAbove j)) := by
  induction m with
  | zero =>
    rw [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    simp only [Fin.val_zero, pow_zero, one_smul]
    rfl
  | succ m ih =>
    have h1 : ((d X (m + 1)).hom a : C(G, resolutionX X (m + 1))) (x 0) =
        a - (d X m).hom ((a : C(G, resolutionX X m)) (x 0)) := by
      rw [hom_d_succ]
      rfl
    rw [nestedHomeomorph_succ_apply, h1,
      show nestedHomeomorph X (m + 1) (a - (d X m).hom ((a : C(G, resolutionX X m)) (x 0))) =
        nestedHomeomorph X (m + 1) a -
          nestedHomeomorph X (m + 1) ((d X m).hom ((a : C(G, resolutionX X m)) (x 0))) from
        map_sub (nestedLinearEquiv X (m + 1)) _ _,
      ContinuousMap.sub_apply, ih, Fin.sum_univ_succ (n := m + 1)]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.succAbove_zero, Fin.val_succ, pow_succ,
      mul_neg_one, neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg]
    congr 1
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [nestedHomeomorph_succ_apply X m a, Fin.succ_succAbove_zero]
    congr 1
    funext j
    simp only [Fin.tail, Fin.succ_succAbove_succ]
end GroundTheory.ProfCoh
end

-- bundled from GroundTheory.ProfiniteCohomology.FilteredHomology
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

section Elements

variable {R : Type u} [Ring R] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex (ModuleCat.{u} R) c)

theorem exists_iCycles_eq {i : ι} (x : K.X i) (hx : (K.d i (c.next i)).hom x = 0) :
    ∃ z : K.cycles i, (K.iCycles i).hom z = x := by
  refine ⟨(K.sc i).moduleCatCyclesIso.inv ⟨x, hx⟩, ?_⟩
  have := ShortComplex.moduleCatCyclesIso_inv_iCycles_apply (K.sc i) ⟨x, hx⟩
  exact this

theorem shortComplex_homologyπ_eq_zero_iff (S : ShortComplex (ModuleCat.{u} R)) (z : S.cycles) :
    S.homologyπ.hom z = 0 ↔ ∃ w : S.X₁, S.f.hom w = S.iCycles.hom z := by
  have hinj : Function.Injective S.moduleCatHomologyIso.hom.hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have h1 : S.moduleCatHomologyIso.hom.hom (S.homologyπ.hom z) =
      S.moduleCatLeftHomologyData.π.hom (S.moduleCatCyclesIso.hom.hom z) :=
    ShortComplex.π_moduleCatCyclesIso_hom_apply S z
  have h2 : S.moduleCatLeftHomologyData.i.hom (S.moduleCatCyclesIso.hom.hom z) =
      S.iCycles.hom z :=
    ShortComplex.moduleCatCyclesIso_hom_i_apply S z
  have h0 : S.homologyπ.hom z = 0 ↔ S.moduleCatHomologyIso.hom.hom (S.homologyπ.hom z) = 0 :=
    ⟨fun h => by rw [h, map_zero], fun h => hinj (h.trans (map_zero _).symm)⟩
  rw [h0, h1]
  change Submodule.Quotient.mk (p := LinearMap.range S.moduleCatToCycles)
    (S.moduleCatCyclesIso.hom.hom z) = 0 ↔ _
  refine (Submodule.Quotient.mk_eq_zero (LinearMap.range S.moduleCatToCycles)
    (x := (S.moduleCatCyclesIso.hom.hom z : LinearMap.ker S.g.hom))).trans ?_
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, (congrArg S.moduleCatLeftHomologyData.i.hom hw).trans h2⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, (ModuleCat.mono_iff_injective S.moduleCatLeftHomologyData.i).1 inferInstance
      (hw.trans h2.symm)⟩

theorem homologyπ_eq_zero_iff {i : ι} (z : K.cycles i) :
    (K.homologyπ i).hom z = 0 ↔
      ∃ w : K.X (c.prev i), (K.d (c.prev i) i).hom w = (K.iCycles i).hom z :=
  shortComplex_homologyπ_eq_zero_iff (K.sc i) z

end Elements

section Apply

variable {R : Type u} [Ring R] {ι : Type*} {c : ComplexShape ι}
  {K L : HomologicalComplex (ModuleCat.{u} R) c}

theorem hom_f_d_apply (φ : K ⟶ L) (i j : ι) (x : K.X i) :
    (φ.f j).hom ((K.d i j).hom x) = (L.d i j).hom ((φ.f i).hom x) :=
  (congrArg (fun g => ModuleCat.Hom.hom g x) (φ.comm i j)).symm

theorem iCycles_d_apply (K : HomologicalComplex (ModuleCat.{u} R) c) (i j : ι) (z : K.cycles i) :
    (K.d i j).hom ((K.iCycles i).hom z) = 0 := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, K.iCycles_d, ModuleCat.hom_zero,
    LinearMap.zero_apply]

theorem iCycles_cyclesMap_apply (φ : K ⟶ L) (i : ι) (z : K.cycles i) :
    (L.iCycles i).hom ((HomologicalComplex.cyclesMap φ i).hom z) =
      (φ.f i).hom ((K.iCycles i).hom z) :=
  congrArg (fun g => ModuleCat.Hom.hom g z) (HomologicalComplex.cyclesMap_i φ i)

theorem homologyMap_homologyπ_apply (φ : K ⟶ L) (i : ι) (z : K.cycles i) :
    (HomologicalComplex.homologyMap φ i).hom ((K.homologyπ i).hom z) =
      (L.homologyπ i).hom ((HomologicalComplex.cyclesMap φ i).hom z) :=
by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, HomologicalComplex.homologyπ_naturality]
  rfl

end Apply

section Filtered

variable {R : Type u} [Ring R] {ι : Type*} {c : ComplexShape ι}
  {J : Type u} [SmallCategory J] [IsFiltered J]
  {F : J ⥤ HomologicalComplex (ModuleCat.{u} R) c} (t : Cocone F)

omit [IsFiltered J] in
theorem cocone_w_apply {j j' : J} (f : j ⟶ j') (i : ι) (y : (F.obj j).X i) :
    ((t.ι.app j').f i).hom (((F.map f).f i).hom y) = ((t.ι.app j).f i).hom y :=
  congrArg (fun φ : F.obj j ⟶ t.pt => (φ.f i).hom y) (t.w f)

omit [IsFiltered J] in

theorem exists_homologyMap_eq_of_cocone (i : ι)
    (hsurj : ∀ x : t.pt.X i, ∃ (j : J) (y : (F.obj j).X i), ((t.ι.app j).f i).hom y = x)
    (hinj : ∀ (j : J) (y : (F.obj j).X (c.next i)), ((t.ι.app j).f (c.next i)).hom y = 0 →
      ∃ (j' : J) (f : j ⟶ j'), ((F.map f).f (c.next i)).hom y = 0)
    (z : t.pt.homology i) :
    ∃ (j : J) (y : (F.obj j).homology i),
      (HomologicalComplex.homologyMap (t.ι.app j) i).hom y = z := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (t.pt.homologyπ i)).1 inferInstance z
  obtain ⟨j, y, hy⟩ := hsurj ((t.pt.iCycles i).hom z)
  have hdy : ((t.ι.app j).f (c.next i)).hom (((F.obj j).d i (c.next i)).hom y) = 0 := by
    rw [hom_f_d_apply, hy]
    exact iCycles_d_apply t.pt i _ z
  obtain ⟨j', f, hf⟩ := hinj j _ hdy
  rw [hom_f_d_apply] at hf
  obtain ⟨z', hz'⟩ := exists_iCycles_eq (F.obj j') (((F.map f).f i).hom y) hf
  refine ⟨j', (HomologicalComplex.homologyπ (F.obj j') i).hom z', ?_⟩
  rw [homologyMap_homologyπ_apply]
  congr 1
  apply (ModuleCat.mono_iff_injective (t.pt.iCycles i)).1 inferInstance
  rw [iCycles_cyclesMap_apply, hz', cocone_w_apply, hy]

theorem exists_homologyMap_map_eq_zero_of_cocone (i : ι)
    (hsurj : ∀ x : t.pt.X (c.prev i),
      ∃ (j : J) (y : (F.obj j).X (c.prev i)), ((t.ι.app j).f (c.prev i)).hom y = x)
    (hinj : ∀ (j : J) (y : (F.obj j).X i), ((t.ι.app j).f i).hom y = 0 →
      ∃ (j' : J) (f : j ⟶ j'), ((F.map f).f i).hom y = 0)
    (j : J) (y : (F.obj j).homology i)
    (hy : (HomologicalComplex.homologyMap (t.ι.app j) i).hom y = 0) :
    ∃ (j' : J) (f : j ⟶ j'), (HomologicalComplex.homologyMap (F.map f) i).hom y = 0 := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective ((F.obj j).homologyπ i)).1 inferInstance y
  rw [homologyMap_homologyπ_apply, homologyπ_eq_zero_iff, iCycles_cyclesMap_apply] at hy
  obtain ⟨w, hw⟩ := hy
  obtain ⟨j₁, v, hv⟩ := hsurj w
  let m := IsFiltered.max j j₁
  let a : j ⟶ m := IsFiltered.leftToMax j j₁
  let b : j₁ ⟶ m := IsFiltered.rightToMax j j₁
  let e : (F.obj m).X i := ((F.map a).f i).hom (((F.obj j).iCycles i).hom z) -
    ((F.obj m).d (c.prev i) i).hom (((F.map b).f (c.prev i)).hom v)
  have he : ((t.ι.app m).f i).hom e = 0 := by
    simp only [e, map_sub]
    rw [cocone_w_apply, hom_f_d_apply, cocone_w_apply, hv]
    exact sub_eq_zero.2 hw.symm
  obtain ⟨j', g, hg⟩ := hinj m e he
  refine ⟨j', a ≫ g, ?_⟩
  rw [homologyMap_homologyπ_apply, homologyπ_eq_zero_iff, iCycles_cyclesMap_apply]
  refine ⟨((F.map (b ≫ g)).f (c.prev i)).hom v, ?_⟩
  simp only [e, map_sub, sub_eq_zero] at hg
  rw [F.map_comp, F.map_comp, HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [← hom_f_d_apply]
  exact hg.symm

noncomputable def isColimitHomologyMapCocone (i : ι)
    (hsurj : ∀ (n : ι) (x : t.pt.X n),
      ∃ (j : J) (y : (F.obj j).X n), ((t.ι.app j).f n).hom y = x)
    (hinj : ∀ (n : ι) (j : J) (y : (F.obj j).X n), ((t.ι.app j).f n).hom y = 0 →
      ∃ (j' : J) (f : j ⟶ j'), ((F.map f).f n).hom y = 0) :
    IsColimit ((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) c i).mapCocone t) :=
  isColimitOfReflects (forget (ModuleCat.{u} R)) <|
    Types.FilteredColimit.isColimitOf' _ _
      (fun z => by
        obtain ⟨j, y, hy⟩ := exists_homologyMap_eq_of_cocone t i (hsurj i) (hinj (c.next i)) z
        exact ⟨j, y, hy.symm⟩)
      (fun j (x y : (F.obj j).homology i) hxy => by
        have hxy' : (HomologicalComplex.homologyMap (t.ι.app j) i).hom x =
            (HomologicalComplex.homologyMap (t.ι.app j) i).hom y := hxy
        obtain ⟨j', f, h⟩ := exists_homologyMap_map_eq_zero_of_cocone t i (hsurj (c.prev i))
          (hinj i) j (x - y) (by rw [map_sub, hxy', sub_self])
        have h' : (HomologicalComplex.homologyMap (F.map f) i).hom x =
            (HomologicalComplex.homologyMap (F.map f) i).hom y := by
          rw [← sub_eq_zero, ← map_sub]
          exact h
        exact ⟨j', f, h'⟩)

end Filtered

end GroundTheory.ProfCoh
end

-- bundled from GroundTheory.ProfiniteCohomology.ProcyclicDefs
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

variable {G : Type*} [Group G] [TopologicalSpace G]

def IsTopologicalGenerator (σ : G) : Prop :=
  Dense (Subgroup.zpowers σ : Set G)

structure IsZHatGenerator (σ : G) : Prop where

  dense : IsTopologicalGenerator σ

  exists_hom : ∀ n : ℕ, 0 < n → ∃ φ : G →* Multiplicative (ZMod n),
    IsOpen (φ.ker : Set G) ∧ φ σ = Multiplicative.ofAdd 1

theorem _root_.IsLocallyConstant.eq_of_eqOn_dense {X Y : Type*} [TopologicalSpace X] {f g : X → Y}
    (hf : IsLocallyConstant f) (hg : IsLocallyConstant g) {s : Set X} (hs : Dense s)
    (h : Set.EqOn f g s) : f = g := by
  let _ : TopologicalSpace Y := ⊥
  have : DiscreteTopology Y := ⟨rfl⟩
  exact Continuous.ext_on hs hf.continuous hg.continuous h

namespace IsTopologicalGenerator

variable {σ : G}

theorem eq_of_forall_zpow (hσ : IsTopologicalGenerator σ) {Y : Type*} {f g : G → Y}
    (hf : IsLocallyConstant f) (hg : IsLocallyConstant g) (h : ∀ n : ℤ, f (σ ^ n) = g (σ ^ n)) :
    f = g :=
  hf.eq_of_eqOn_dense hg hσ fun _ ⟨n, hn⟩ => hn ▸ h n

theorem eq_of_forall_zpow_pi (hσ : IsTopologicalGenerator σ) {n : ℕ} {Y : Type*}
    {f g : (Fin n → G) → Y} (hf : IsLocallyConstant f) (hg : IsLocallyConstant g)
    (h : ∀ m : Fin n → ℤ, f (fun i => σ ^ m i) = g (fun i => σ ^ m i)) : f = g := by
  refine hf.eq_of_eqOn_dense hg (s := Set.univ.pi fun _ => (Subgroup.zpowers σ : Set G))
    (dense_pi Set.univ fun _ _ => hσ) fun x hx => ?_
  choose m hm using fun i => hx i (Set.mem_univ i)
  have hx' : x = fun i => σ ^ m i := funext fun i => (hm i).symm
  rw [hx']
  exact h m

end IsTopologicalGenerator

end GroundTheory.ProfCoh
end


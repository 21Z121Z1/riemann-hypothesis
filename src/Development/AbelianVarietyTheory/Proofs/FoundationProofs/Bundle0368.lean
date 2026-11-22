import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2095
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0367
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0365
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.RamifiedPlacesSplitEigen
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0037
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0260
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0347
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearActionDualWeylTensor

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AutomorphicRepDualPairing
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology

noncomputable section

namespace GlobalTheory.FrameAut.VecProj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
variable {S : Type} [AddCommGroup S] [Module ℂ S]

def forms (ρ : Representation ℂ (infU E n) S) : Submodule ℂ (S →ₗ[ℂ] (UA E n → ℂ)) where
  carrier := {f | (∀ v, f v ∈ autU E n) ∧ ∀ (x : infU E n) v, f (ρ x v) = RU E n x (f v)}
  add_mem' ha hb := ⟨fun v => add_mem (ha.1 v) (hb.1 v), fun x v => by
    rw [LinearMap.add_apply, LinearMap.add_apply, ha.2, hb.2, map_add]⟩
  zero_mem' := ⟨fun _ => zero_mem _, fun _ _ => rfl⟩
  smul_mem' c _ ha := ⟨fun v => Submodule.smul_mem _ c (ha.1 v), fun x v => by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, ha.2, map_smul]⟩

variable (E n S) in

def post : Representation ℂ (finU E n) (S →ₗ[ℂ] (UA E n → ℂ)) where
  toFun k := LinearMap.llcomp ℂ _ _ _ (RU E n k)
  map_one' := LinearMap.ext fun f => LinearMap.ext fun v => funext fun g => congrArg (f v) (mul_one g)
  map_mul' a b := LinearMap.ext fun f => LinearMap.ext fun v => funext fun g => congrArg (f v) (mul_assoc g a b).symm

@[simp] theorem post_apply (k : finU E n) (f : S →ₗ[ℂ] (UA E n → ℂ)) (v : S) :
    post E n S k f v = RU E n k (f v) := rfl

theorem post_mem (ρ : Representation ℂ (infU E n) S) (k : finU E n) (f : S →ₗ[ℂ] (UA E n → ℂ))
    (h : f ∈ forms ρ) : post E n S k f ∈ forms ρ :=
  ⟨fun v => RU_mem_autU _ _ (h.1 v), fun x v => by
    rw [post_apply, post_apply, h.2, RU_RU, RU_RU, fin_mul_inf k.2 x.2]⟩

def rep (ρ : Representation ℂ (infU E n) S) : Representation ℂ (finU E n) (forms ρ) :=
  GlobalTheory.PRep.sub (post E n S) (forms ρ) (post_mem ρ)

@[simp] theorem rep_val (ρ : Representation ℂ (infU E n) S) (k : finU E n) (f : forms ρ) :
    (rep ρ k f).1 = post E n S k f.1 := rfl

end GlobalTheory.FrameAut.VecProj

namespace GlobalTheory.FrameAut.VecProj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
variable {S : Type} [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S]

def ev (ρ : Representation ℂ (infU E n) S) (v : S) : forms ρ →ₗ[ℂ] autU E n where
  toFun f := ⟨f.1 v, f.2.1 v⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def form (B : autU E n →ₗ⋆[ℂ] autU E n →ₗ[ℂ] ℂ) (ρ : Representation ℂ (infU E n) S) :
    forms ρ →ₗ⋆[ℂ] forms ρ →ₗ[ℂ] ℂ :=
  ∑ i, (B.comp (ev ρ (Module.finBasis ℂ S i))).compl₂ (ev ρ (Module.finBasis ℂ S i))

theorem form_apply (B : autU E n →ₗ⋆[ℂ] autU E n →ₗ[ℂ] ℂ) (ρ : Representation ℂ (infU E n) S) (f g : forms ρ) :
    form B ρ f g = ∑ i, B (ev ρ (Module.finBasis ℂ S i) f) (ev ρ (Module.finBasis ℂ S i) g) := by
  simp [form, LinearMap.sum_apply]

end GlobalTheory.FrameAut.VecProj

namespace GlobalTheory.FrameAut.VecProj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
variable {S : Type} [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S]

theorem form_herm (B : autU E n →ₗ⋆[ℂ] autU E n →ₗ[ℂ] ℂ) (hh : ∀ u v, star (B u v) = B v u)
    (ρ : Representation ℂ (infU E n) S) (f g : forms ρ) : star (form B ρ f g) = form B ρ g f := by
  rw [form_apply, form_apply, star_sum]
  exact Finset.sum_congr rfl fun i _ => hh _ _

theorem form_nonneg (B : autU E n →ₗ⋆[ℂ] autU E n →ₗ[ℂ] ℂ) (hp : ∀ v, 0 ≤ (B v v).re)
    (ρ : Representation ℂ (infU E n) S) (f : forms ρ) : 0 ≤ (form B ρ f f).re := by
  rw [form_apply, Complex.re_sum]
  exact Finset.sum_nonneg fun i _ => hp _

theorem form_def (B : autU E n →ₗ⋆[ℂ] autU E n →ₗ[ℂ] ℂ) (hh : ∀ u v, star (B u v) = B v u)
    (hp : ∀ v, 0 ≤ (B v v).re) (hd : ∀ v, B v v = 0 → v = 0)
    (ρ : Representation ℂ (infU E n) S) (f : forms ρ) (h0 : form B ρ f f = 0) : f = 0 := by
  rw [form_apply] at h0
  have hre : ∑ i, (B (ev ρ (Module.finBasis ℂ S i) f) (ev ρ (Module.finBasis ℂ S i) f)).re = 0 := by
    rw [← Complex.re_sum, h0, Complex.zero_re]
  have hz : ∀ i, B (ev ρ (Module.finBasis ℂ S i) f) (ev ρ (Module.finBasis ℂ S i) f) = 0 := by
    intro i
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hp _)).1 hre i (Finset.mem_univ i)
    have h2 : (B (ev ρ (Module.finBasis ℂ S i) f) (ev ρ (Module.finBasis ℂ S i) f)).im = 0 := by
      have := congrArg Complex.im (hh (ev ρ (Module.finBasis ℂ S i) f) (ev ρ (Module.finBasis ℂ S i) f))
      rw [Complex.star_def, Complex.conj_im] at this
      linarith
    exact Complex.ext h1 h2
  apply Subtype.ext
  refine (Module.finBasis ℂ S).ext fun i => ?_
  have := congrArg Subtype.val (hd _ (hz i))
  simpa [ev] using this

theorem form_inv (B : autU E n →ₗ⋆[ℂ] autU E n →ₗ[ℂ] ℂ)
    (hi : ∀ g u v, B (autRep E n g u) (autRep E n g v) = B u v)
    (ρ : Representation ℂ (infU E n) S) (k : finU E n) (f g : forms ρ) :
    form B ρ (rep ρ k f) (rep ρ k g) = form B ρ f g := by
  rw [form_apply, form_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact hi (k : UA E n) (ev ρ (Module.finBasis ℂ S i) f) (ev ρ (Module.finBasis ℂ S i) g)

theorem rep_smooth (ρ : Representation ℂ (infU E n) S) (f : forms ρ) :
    IsOpen {k : finU E n | rep ρ k f = f} := by
  let b := Module.finBasis ℂ S
  convert isOpen_iInter_of_finite fun i => (f.2.1 (b i)).level using 1
  ext k
  rw [Set.mem_iInter]
  exact ⟨fun h i => LinearMap.congr_fun (congrArg Subtype.val h) (b i), fun h => Subtype.ext (b.ext h)⟩

theorem rep_fd (ρ : Representation ℂ (infU E n) S) (K : Subgroup (finU E n)) (hK : IsOpen (K : Set (finU E n))) :
    FiniteDimensional ℂ (GlobalTheory.PRep.fixed (rep ρ) K) := by
  have hM := GlobalTheory.T.finiteDimensional_vectorValued_definiteUnitaryForms E n S ρ K hK ((GlobalTheory.PRep.fixed (rep ρ) K).map (forms ρ).subtype) (by
    rintro _ ⟨g, hg, rfl⟩
    refine ⟨fun v γ hγ x => (g.2.1 v).left γ hγ x, g.2.2, fun k hk v => ?_⟩
    have h1 : rep ρ k g = g := by
      have := hg ⟨k, hk⟩
      rw [MonoidHom.one_apply, Units.val_one, one_smul] at this
      exact this
    exact LinearMap.congr_fun (congrArg Subtype.val h1) v)
  exact LinearEquiv.finiteDimensional
    (Submodule.equivMapOfInjective _ (forms ρ).injective_subtype _).symm

end GlobalTheory.FrameAut.VecProj

namespace GlobalTheory.FrameAut.VecProj

theorem exists_autRep_projection : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (B : autU E n →ₗ⋆[ℂ] autU E n →ₗ[ℂ] ℂ), (∀ u v, star (B u v) = B v u) → (∀ v, 0 ≤ (B v v).re) → (∀ v, B v v = 0 → v = 0) → (∀ g u v, B (autRep E n g u) (autRep E n g v) = B u v) → ∀ (S : Type) [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S] (ρ : Representation ℂ (infU E n) S), Submodule.span ℂ (Set.range ρ) = ⊤ → ∀ f : S →ₗ[ℂ] (UA E n → ℂ), f ≠ 0 → (∀ v, IsAutFormU (f v)) → (∀ (x : infU E n) v, f (ρ x v) = RU E n x (f v)) → ∃ π, IsAutRepU π ∧ ∃ f' : S →ₗ[ℂ] (UA E n → ℂ), f' ≠ 0 ∧ (∀ v, f' v ∈ π) ∧ (∀ (x : infU E n) v, f' (ρ x v) = RU E n x (f' v)) ∧ ∀ (κ : Type) (R : Finset κ) (s : κ → UA E n) (c : ℂ), (∀ i ∈ R, s i ∈ finU E n) → (∀ v, ∑ i ∈ R, RU E n (s i) (f v) = c • f v) → ∀ v, ∑ i ∈ R, RU E n (s i) (f' v) = c • f' v := by
  intro E _ _ _ n B hh hp hd hi S _ _ _ ρ hsp f hf0 hfa hfe
  classical
  have hfA : f ∈ forms ρ := ⟨fun v => hfa v, hfe⟩
  have hx : (⟨f, hfA⟩ : forms ρ) ≠ 0 := fun h => hf0 (congrArg Subtype.val h)
  obtain ⟨U, P, hU0, hUst, hUirr, hPU, hPeq, hPx⟩ :=
    GlobalTheory.AdmissibleProjection.exists_irreducible_equivariant_projection (finU E n) (forms ρ) (rep ρ)
      (form B ρ) (form_herm B hh ρ) (form_nonneg B hp ρ) (form_def B hh hp hd ρ) (form_inv B hi ρ)
      (GlobalTheory.T.definiteUnitaryFinitePoints_exists_openCompact E n) (rep_smooth ρ) (rep_fd ρ) ⟨f, hfA⟩ hx
  let M : Submodule ℂ (S →ₗ[ℂ] (UA E n → ℂ)) := U.map (forms ρ).subtype
  have hM0 : M ≠ ⊥ := by
    intro h
    apply hU0
    rw [Submodule.eq_bot_iff]
    intro u hu
    have : u.1 ∈ M := ⟨u, hu, rfl⟩
    rw [h, Submodule.mem_bot] at this
    exact Subtype.ext this
  have hMf : ∀ g ∈ M, (∀ v, IsAutFormU (g v)) ∧ ∀ (x : infU E n) v, g (ρ x v) = RU E n x (g v) := by
    rintro _ ⟨u, -, rfl⟩
    exact ⟨fun v => u.2.1 v, u.2.2⟩
  have hMk : ∀ k ∈ finU E n, ∀ g ∈ M, (RU E n k) ∘ₗ g ∈ M := by
    rintro k hk _ ⟨u, hu, rfl⟩
    exact ⟨rep ρ ⟨k, hk⟩ u, hUst _ u hu, rfl⟩
  have hMirr : ∀ N ≤ M, (∀ k ∈ finU E n, ∀ g ∈ N, (RU E n k) ∘ₗ g ∈ N) → N = ⊥ ∨ N = M := by
    intro N hNM hN
    let N' : Submodule ℂ (forms ρ) := N.comap (forms ρ).subtype
    have hN'U : N' ≤ U := by
      intro u hu
      obtain ⟨w, hw, hwu⟩ := hNM hu
      rw [← Subtype.ext hwu]
      exact hw
    have hN'st : ∀ g, ∀ u ∈ N', rep ρ g u ∈ N' := fun g u hu => hN g.1 g.2 u.1 hu
    have hNe : N'.map (forms ρ).subtype = N := by
      rw [Submodule.map_comap_subtype]
      exact inf_eq_right.2 (hNM.trans (Submodule.map_subtype_le _ _))
    rcases hUirr N' hN'U hN'st with h | h
    · left; rw [← hNe, h, Submodule.map_bot]
    · right; rw [← hNe, h]
  have hπ := GlobalTheory.FrameAut.VecForms.isAutRepU_span_values E n S ρ hsp M hM0 hMf hMk hMirr
  refine ⟨_, hπ, (P ⟨f, hfA⟩).1, fun h => hPx (Subtype.ext h), fun v => Submodule.subset_span
    ⟨(P ⟨f, hfA⟩).1, ⟨_, hPU _, rfl⟩, v, rfl⟩, (P ⟨f, hfA⟩).2.2, ?_⟩
  intro κ R s c hs hsum v
  have hA : ∑ i ∈ R.attach, rep ρ ⟨s i.1, hs i.1 i.2⟩ ⟨f, hfA⟩ = c • (⟨f, hfA⟩ : forms ρ) := by
    apply Subtype.ext
    refine LinearMap.ext fun w => ?_
    rw [Submodule.coe_sum, LinearMap.sum_apply, Submodule.coe_smul, LinearMap.smul_apply, ← hsum w]
    exact Finset.sum_attach R (fun i => RU E n (s i) (f w))
  have hB := congrArg P hA
  rw [map_sum, map_smul] at hB
  simp only [hPeq] at hB
  have := LinearMap.congr_fun (congrArg Subtype.val hB) v
  rw [Submodule.coe_sum, LinearMap.sum_apply, Submodule.coe_smul, LinearMap.smul_apply] at this
  rw [← this]
  exact (Finset.sum_attach R (fun i => RU E n (s i) ((P ⟨f, hfA⟩).1 v))).symm

end GlobalTheory.FrameAut.VecProj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FibreIff
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

namespace GlobalTheory.FlatRow

section Lie

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {R : Type} [CommRing R] {x : Sp R ⟶ S} {A : Over (Sp R)} [GrpObj A]
  {φ : A.left ⟶ G.left} {m : ℕ}

theorem exists_lift (h : IsGrpPullback A G x φ) (u : FramedFlatCoordinates.epsAt x ⟶ G) :
    ∃ v : epsR R ⟶ A, v.left ≫ φ = u.left :=
  let ⟨e, he⟩ := LiePull.exists_pushEquiv h (epsR R) (spMap (algebraMap R (DualNumber R)) ≫ x) rfl
  ⟨e.symm u, by rw [← he, e.apply_symm_apply]⟩

theorem fibre_iff (h : IsGrpPullback A G x φ) {v : Fin m → (epsR R ⟶ A)} {u : Fin m → (FramedFlatCoordinates.epsAt x ⟶ G)}
    (hu : ∀ i, (v i).left ≫ φ = (u i).left) :
    (∀ (c : Fin m → R) (w : epsR R ⟶ A) (w' : FramedFlatCoordinates.epsAt x ⟶ G), w.left ≫ φ = w'.left →
      (IsLieComb c v w ↔ FramedFlatCoordinates.IsCombination x c (fun i => (u i).left) w')) ∧
    ∀ {O : Type} [CommRing O] {a : OAct O A} {b : OAct O G}, (∀ c, (a.act c).left ≫ φ = φ ≫ (b.act c).left) →
      ∀ χ : O →+* R, EigenvectorLieDegree.IsEigBasis a χ v ↔ FramedFlatCoordinates.IsEigenBasis b x χ u := by
  obtain ⟨e, he⟩ := LiePull.exists_pushEquiv h (epsR R) (spMap (algebraMap R (DualNumber R)) ≫ x) rfl
  obtain ⟨e₀, he₀⟩ := LiePull.exists_pushEquiv h (𝟙_ (Over (Sp R))) x (Category.id_comp _).symm
  obtain rfl : u = fun i => e (v i) := funext fun i => Over.OverMorphism.ext ((hu i).symm.trans (he _).symm)
  have one : (1 : Over.mk x ⟶ G).left = η[A].left ≫ φ := by
    rw [← map_one e₀, he₀, Hom.one_def, toUnit_unit, Category.id_comp]
  have sc : ∀ c : R, spMap (epsScaleR c) ≫ spMap (algebraMap R (DualNumber R)) =
      spMap (algebraMap R (DualNumber R)) := fun c => by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have fs : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _ := by
    refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
    ext a
    simp
  have hR : ∀ (c : R) (u v : epsR R ⟶ A), u.left = spMap (epsScaleR c) ≫ v.left ↔
      (e u).left = spMap (epsScaleR c) ≫ (e v).left := fun c u v => by
    rw [he, he]
    refine ⟨fun E => by rw [E]; exact Category.assoc _ _ _,
      fun E => h.1.hom_ext (E.trans (Category.assoc _ _ _).symm) ?_⟩
    refine (Over.w u).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))
    exact (congrArg (spMap (epsScaleR c) ≫ ·) (Over.w v)).trans (sc c)
  have pr : ∀ u : Fin m → (epsR R ⟶ A), e (List.ofFn u).prod = (List.ofFn fun i => e (u i)).prod := fun u => by
    rw [map_list_prod, List.map_ofFn]; rfl
  have hC : ∀ (c : Fin m → R) (w : epsR R ⟶ A),
      IsLieComb c v w ↔ FramedFlatCoordinates.IsCombination x c (fun i => (e (v i)).left) (e w) := fun c w => by
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨fun i => e (u i), fun i => (hR _ _ _).1 (hu i), pr u⟩
    · rintro ⟨u, hu, hw⟩
      refine ⟨fun i => e.symm (u i), fun i => (hR _ _ _).2 (by simpa using hu i), e.injective ?_⟩
      rw [pr, hw]
      simp
  refine ⟨fun c w w' hw => ?_, fun {O} _ a b hab χ => ?_⟩
  · obtain rfl : w' = e w := Over.OverMorphism.ext (hw.symm.trans (he _).symm)
    exact hC c w
  have hP : ∀ v : epsR R ⟶ A, EigenvectorLieDegree.IsEigVec a χ v ↔ FramedFlatCoordinates.IsEigenTangent b x χ (e v) := fun v => by
    refine and_congr ?_ (forall_congr' fun c => ?_)
    · rw [one, he, IsTangent]
      refine ⟨fun E => by rw [← E]; exact (Category.assoc _ _ _).symm,
        fun E => h.1.hom_ext ((Category.assoc _ _ _).trans E) ?_⟩
      refine ((Category.assoc _ _ _).trans ?_).trans (Over.w η[A]).symm
      exact (congrArg (spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ ·) (Over.w v)).trans fs
    · have E : e (v ≫ a.act c) = e v ≫ b.act c := Over.OverMorphism.ext (by
        rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, hab, Category.assoc])
      rw [hR, E]
  refine and_congr (forall_congr' fun i => hP _) (Iff.trans ?_ e.surjective.forall.symm)
  exact forall_congr' fun w => imp_congr (hP w) (existsUnique_congr fun c => hC c w)

end Lie

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H}

def EigStable {S : Scheme.{0}} (T : SAB H S) (c : Coeff l) : Prop :=
  ∀ (R R' : Type) [CommRing R] [CommRing R'] (g : R →+* R') (j : c.F →+* R) (x : Sp R ⟶ S) (τ : E →+* ℂ) (m : ℕ)
    (v : Fin m → (FramedFlatCoordinates.epsAt x ⟶ T.G)) (v' : Fin m → (FramedFlatCoordinates.epsAt (spMap g ≫ x) ⟶ T.G)),
    FramedFlatCoordinates.IsEigenBasis T.act x (FramedFlatCoordinates.chr c τ j) v →
    (∀ i, (v' i).left = spMap (Chart.dualMapR g) ≫ (v i).left) →
    FramedFlatCoordinates.IsEigenBasis T.act (spMap g ≫ x) (FramedFlatCoordinates.chr c τ (g.comp j)) v'

variable {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {U : (Xo.XF c).Opens} {τ : E →+* ℂ}

def IsSqNorm (sig : FramedFlatCoordinates.Rule Y U τ) (s : c.F →+* ℂ) (κ : ℝ) : Prop :=
  ∃ (a : FramedFlatCoordinates.Framed Y U τ ℂ s) (y : Sp ℂ ⟶ Xo.XF c) (t : SAB H (Sp ℂ)) (v : Fin Dw.p → (epsR ℂ ⟶ t.G))
    (w : Fin Dw.q → (epsR ℂ ⟶ t.G)) (g : ℕ) (u : HolUnif t.G t.PP.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ)
    (zv : Fin Dw.p → Fin g → ℂ) (zw : Fin Dw.q → Fin g → ℂ),
    LiesOver a y ∧ IsFibre a t v w ∧ u.IsAH Hm χ ∧ (∀ i, u.IsDiff (zv i) (v i)) ∧ (∀ i, u.IsDiff (zw i) (w i)) ∧
    0 < EigenbasisGramSquares.gramSq Hm zv ∧ 0 < EigenbasisGramSquares.gramSq Hm zw ∧
    κ = ‖sig ℂ s a‖ ^ 2 * (EigenbasisGramSquares.gramSq Hm zv / EigenbasisGramSquares.gramSq Hm zw)

def IsValue (sig : FramedFlatCoordinates.Rule Y U τ) {ℓ : ℕ} [Fact ℓ.Prime] {K : Type} [Field K] (i : K →+* ℂ_[ℓ]) (φ : c.F →+* K)
    (x : ℝ) : Prop :=
  ∃ (V : ValuationSubring K) (a : FramedFlatCoordinates.Framed Y U τ K φ) (y : Sp K ⟶ Xo.XF c) (t : SAB H (Sp K))
    (v : Fin Dw.p → (epsR K ⟶ t.G)) (w : Fin Dw.q → (epsR K ⟶ t.G)) (𝒢 : Over (Sp V)) (_ : GrpObj 𝒢)
    (b : OAct (𝓞 E) 𝒢) (ψ : t.G.left ⟶ 𝒢.left) (χ χ' : 𝓞 E →+* V) (u : Fin Dw.p → (epsR V ⟶ 𝒢))
    (u' : Fin Dw.q → (epsR V ⟶ 𝒢)),
    (∀ z : K, z ∈ V ↔ ‖i z‖ ≤ 1) ∧ LiesOver a y ∧ IsFibre a t v w ∧ IsSemiAbelian 𝒢 ∧
    IsGrpPullback t.G 𝒢 (spMap (algebraMap V K)) ψ ∧ (∀ z, (t.act.act z).left ≫ ψ = ψ ≫ (b.act z).left) ∧
    (algebraMap V K).comp χ = FramedFlatCoordinates.chr c τ φ ∧ (algebraMap V K).comp χ' = FramedFlatCoordinates.chr c (conjEmb τ) φ ∧
    EigenvectorLieDegree.IsEigBasis b χ u ∧ EigenvectorLieDegree.IsEigBasis b χ' u' ∧ (∀ k, IsVecOver (algebraMap V K) ψ (u k) (v k)) ∧
    (∀ k, IsVecOver (algebraMap V K) ψ (u' k) (w k)) ∧ ‖i (sig K φ a)‖ = (ℓ : ℝ) ^ (-x)

end GlobalTheory.FlatRow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeightModuleInvariantPairing
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology

noncomputable section

namespace GlobalTheory.AutPairing

set_option maxHeartbeats 1000000 in

theorem exists_invariant_pairing : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (sh : ι → ℤ)
    (lam : ι → DomWeight n), (∀ τ a, (lam τ).w a = (mu τ a : ℤ) + sh τ) →
    ∃ B : Formalism.L2.DIV.VV ℂ lam →ₗ[ℂ] NablaT ℂ n mu →ₗ[ℂ] ℂ, (∀ u, u ≠ 0 → ∃ v, B v u ≠ 0) ∧
      ∀ (g : ι → GL (Fin n) ℂ) v u, B (Formalism.L2.DIV.rhoK lam g v) (wtOp ℂ n mu sh g u) = B v u := by
  intro n ι _ _ mu sh lam hlam
  have hE : ∀ τ, ∃ e : nablaSq ℂ n (lam τ) →ₗ[ℂ] Formalism.GradedWeylDivisibility.dualWeyl ℂ n n (Formalism.CohomologicalDescent.LD.res n (mu τ)),
      Function.Surjective e ∧ ∀ (g : GL (Fin n) ℂ) v,
        (e (GlobalTheory.Branching.sqRep ℂ n (lam τ) g v) : MvPolynomial (Fin n × Fin n) ℂ) =
          detPow ℂ n g (sh τ) • Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (g : Matrix (Fin n) (Fin n) ℂ).transpose
            (e v : MvPolynomial (Fin n × Fin n) ℂ) :=
    fun τ => GlobalTheory.Branching.exists_surjective_detPowMul_dualWeyl n (Formalism.CohomologicalDescent.LD.res n (mu τ)) (sh τ) (lam τ) (fun a => hlam τ a)
  choose e he_surj he_eq using hE
  have hF : ∀ τ, ∃ b : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] ℂ,
      (∀ u ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ n n (Formalism.CohomologicalDescent.LD.res n (mu τ)), u ≠ 0 →
        ∃ v ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ n n (Formalism.CohomologicalDescent.LD.res n (mu τ)), b v u ≠ 0) ∧
      ∀ (g : GL (Fin n) ℂ) v u, b (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (g : Matrix (Fin n) (Fin n) ℂ).transpose v)
        (Formalism.UG.dwAct ℂ n n g u) = b v u :=
    fun τ => GlobalTheory.T.dual_weyl_invariant_pairing n (Formalism.CohomologicalDescent.LD.res n (mu τ))
  choose b hb_sep hb_inv using hF
  let bt : ∀ τ, nablaSq ℂ n (lam τ) →ₗ[ℂ] Formalism.GradedWeylDivisibility.dualWeyl ℂ n n (Formalism.CohomologicalDescent.LD.res n (mu τ)) →ₗ[ℂ] ℂ :=
    fun τ => ((b τ).compl₂ (Submodule.subtype _)).comp ((Submodule.subtype _).comp (e τ))
  have bt_apply : ∀ τ v u, bt τ v u =
      b τ (e τ v : MvPolynomial (Fin n × Fin n) ℂ) (u : MvPolynomial (Fin n × Fin n) ℂ) := fun _ _ _ => rfl
  have bt_sep : ∀ τ u, u ≠ 0 → ∃ v, bt τ v u ≠ 0 := by
    intro τ u hu
    have hu' : (u : MvPolynomial (Fin n × Fin n) ℂ) ≠ 0 := fun h => hu (Subtype.ext h)
    obtain ⟨v, hv, hne⟩ := hb_sep τ u u.2 hu'
    obtain ⟨w, hw⟩ := he_surj τ ⟨v, hv⟩
    exact ⟨w, by rw [bt_apply, hw]; exact hne⟩
  have bt_inv : ∀ τ (g : GL (Fin n) ℂ) v u,
      bt τ (GlobalTheory.Branching.sqRep ℂ n (lam τ) g v) (Formalism.UG.dualWeylRep ℂ n n _ g u) =
        detPow ℂ n g (sh τ) * bt τ v u := by
    intro τ g v u
    rw [bt_apply, bt_apply, he_eq]
    have h1 : (Formalism.UG.dualWeylRep ℂ n n (Formalism.CohomologicalDescent.LD.res n (mu τ)) g u : MvPolynomial (Fin n × Fin n) ℂ) =
        Formalism.UG.dwAct ℂ n n g u := rfl
    rw [h1, map_smul, LinearMap.smul_apply, hb_inv, smul_eq_mul]
  haveI : ∀ τ, FiniteDimensional ℂ (Formalism.GradedWeylDivisibility.dualWeyl ℂ n n (Formalism.CohomologicalDescent.LD.res n (mu τ))) :=
    (GlobalTheory.T.weight_module_finite_continuous n ι mu sh).1
  obtain ⟨Bm, hBm, hBm_sep⟩ := GlobalTheory.T.tensor_product_nondegenerate_pairing ι (fun τ => nablaSq ℂ n (lam τ))
    (fun τ => Formalism.GradedWeylDivisibility.dualWeyl ℂ n n (Formalism.CohomologicalDescent.LD.res n (mu τ))) bt bt_sep
  obtain ⟨B, hB, -⟩ := GlobalTheory.CoefIrred.vv_universal ι n lam (Module.Dual ℂ (NablaT ℂ n mu)) Bm
  refine ⟨B, fun u hu => ?_, fun g => ?_⟩
  · obtain ⟨v, hv⟩ := hBm_sep u hu
    exact ⟨GlobalTheory.CoefIrred.tenMul lam v, by rw [hB]; exact hv⟩
  · have hc : ((∏ τ, Matrix.GeneralLinearGroup.det (g τ) ^ (-sh τ) : ℂˣ) : ℂ) *
        ∏ τ, detPow ℂ n (g τ) (sh τ) = 1 := by
      simp only [detPow]
      rw [← Units.coe_prod, ← Units.val_mul, ← Finset.prod_mul_distrib]
      simp [← zpow_add]
    have hpure : ∀ x y, B (Formalism.L2.DIV.rhoK lam g (GlobalTheory.CoefIrred.tenMul lam x))
        (wtOp ℂ n mu sh g (PiTensorProduct.tprod ℂ y)) = B (GlobalTheory.CoefIrred.tenMul lam x) (PiTensorProduct.tprod ℂ y) := by
      intro x y
      rw [GlobalTheory.DefU.rhoK_tenMul, hB, hB, wtOp_apply, GlobalTheory.SemilinTransport.grp_tprod, map_smul, hBm, hBm, smul_eq_mul]
      simp_rw [bt_inv]
      rw [Finset.prod_mul_distrib, ← mul_assoc, hc, one_mul]
    have hten : ∀ x u, B (Formalism.L2.DIV.rhoK lam g (GlobalTheory.CoefIrred.tenMul lam x)) (wtOp ℂ n mu sh g u) =
        B (GlobalTheory.CoefIrred.tenMul lam x) u := by
      intro x u
      induction u using PiTensorProduct.induction_on with
      | smul_tprod c y => rw [map_smul, map_smul, map_smul, hpure]
      | add a a' ha ha' => rw [map_add, map_add, map_add, ha, ha']
    have h1 : ∀ x, ((B.comp (Formalism.L2.DIV.rhoK lam g)).compl₂ (wtOp ℂ n mu sh g)) (GlobalTheory.CoefIrred.tenMul lam x) = Bm x := by
      intro x
      refine LinearMap.ext fun u => ?_
      rw [LinearMap.compl₂_apply, LinearMap.comp_apply, hten, hB]
    have h2 := (GlobalTheory.CoefIrred.vv_universal ι n lam (Module.Dual ℂ (NablaT ℂ n mu)) Bm).unique h1 hB
    intro v u
    have := LinearMap.congr_fun (LinearMap.congr_fun h2 v) u
    simpa using this

end GlobalTheory.AutPairing

end
end


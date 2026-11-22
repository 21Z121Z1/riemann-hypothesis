import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0610
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0635
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0169
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0189
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueLiftSpecOfIsLocalizationAway
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankEqZeroIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0626
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0036
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0619
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0628
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameMatrixHasSum
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLaw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsTangentEquiv

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellsOfChartsPolynomial
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)

namespace GlobalTheory.GrCl

theorem spMap_comp_spMap_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

theorem normal_stalk_iff {X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion f] (x : X) :
    (IsDomain (Y.presheaf.stalk (f x)) ∧ IsIntegrallyClosed (Y.presheaf.stalk (f x))) ↔
      (IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)) := by
  let e := (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
  exact ⟨fun ⟨_, _⟩ => ⟨e.symm.toMulEquiv.isDomain _, .of_equiv e⟩,
    fun ⟨_, _⟩ => ⟨e.toMulEquiv.isDomain _, .of_equiv e.symm⟩⟩

theorem normal_sp_mvPolynomial {Z : Scheme.{0}} (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z) {R : Type} [CommRing R]
    (χ : Sp R ⟶ Z) [IsOpenImmersion χ] (V : Type) [Finite V] :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp (MvPolynomial V R)) := by
  obtain ⟨r, ⟨e⟩⟩ := Finite.exists_equiv_fin V
  have h := GlobalTheory.isNormalScheme_sp_mvPolynomial R r fun x => (normal_stalk_iff χ x).1 (hn _)
  let φ : CommRingCat.of (MvPolynomial (Fin r) R) ≅ CommRingCat.of (MvPolynomial V R) :=
    (MvPolynomial.renameEquiv R e.symm).toRingEquiv.toCommRingCatIso
  exact fun x => (normal_stalk_iff (Spec.map φ.hom) x).1 (h _)

theorem flat_spMap_C (R V : Type) [CommRing R] : Flat (spMap (MvPolynomial.C : R →+* MvPolynomial V R)) := by
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  exact RingHom.flat_algebraMap_iff.2 (inferInstance : Module.Flat R (MvPolynomial V R))

theorem exists_spMap_fac {X : Scheme.{0}} {R S : Type} [CommRing R] [CommRing S] (χ : Sp R ⟶ X) [IsOpenImmersion χ]
    (w : Sp S ⟶ X) (h : Set.range w ⊆ Set.range χ) : ∃ φ : R →+* S, spMap φ ≫ χ = w := by
  refine ⟨(Spec.preimage (IsOpenImmersion.lift χ w h)).hom, ?_⟩
  show Spec.map (Spec.preimage _) ≫ _ = _
  rw [Spec.map_preimage]
  exact IsOpenImmersion.lift_fac _ _ _

theorem iUnion_inter_chart {O : Type} [CommRing O] {Z P : Scheme.{0}} {s : Z ⟶ Sp O} {N : ℕ} {p₁ : P ⟶ Z}
    {p₂ : P ⟶ PSpace O N} (hP : IsPullback p₁ p₂ s (PSpace.str O N)) (ch : Charts Z) (g : ∀ a, O →+* ch.R a)
    {V J : Type} (ξ : ∀ a, J → Fin (N + 1) → MvPolynomial V (ch.R a)) (hg : ∀ a, ch.χ a ≫ s = spMap (g a))
    (hglue : ∀ (K : Type) [Field K] (a a' : ch.ι) (φ : ch.R a →+* K) (j' : J) (ψ' : MvPolynomial V (ch.R a') →+* K),
      spMap φ ≫ ch.χ a = spMap (ψ'.comp MvPolynomial.C) ≫ ch.χ a' →
        ∃ (j : J) (ψ : MvPolynomial V (ch.R a) →+* K) (u : Kˣ), ψ.comp MvPolynomial.C = φ ∧
          ψ' ∘ ξ a' j' = (u : K) • (ψ ∘ ξ a j))
    (i : ∀ k : ch.ι × J, Sp (MvPolynomial V (ch.R k.1)) ⟶ P)
    (h₁ : ∀ k, i k ≫ p₁ = spMap MvPolynomial.C ≫ ch.χ k.1)
    (h₂ : ∀ k, ∃ hv, i k ≫ p₂ = pt (MvPolynomial.C.comp (g k.1)) (ξ k.1 k.2) hv) (a : ch.ι) :
    (⋃ k, Set.range (i k)) ∩ p₁ ⁻¹' Set.range (ch.χ a) = ⋃ j, Set.range (i (a, j)) := by
  refine Set.Subset.antisymm ?_ (Set.iUnion_subset fun j => ?_)
  · rintro x ⟨hx, hxa⟩
    obtain ⟨⟨a', j'⟩, y, rfl⟩ := Set.mem_iUnion.1 hx
    have := y.isPrime
    let K := y.asIdeal.ResidueField
    let ψ' : MvPolynomial V (ch.R a') →+* K := algebraMap _ _
    have hy : ∀ t, spMap ψ' t = y := fun t => by
      refine PrimeSpectrum.ext ?_
      have ht : t.asIdeal = ⊥ := (Ideal.eq_bot_or_top _).resolve_right t.isPrime.ne_top
      change t.asIdeal.comap ψ' = _
      rw [ht]
      exact Ideal.ker_algebraMap_residueField _
    have e₁ : spMap (ψ'.comp MvPolynomial.C) ≫ ch.χ a' = (spMap ψ' ≫ i (a', j')) ≫ p₁ := by
      rw [Category.assoc, h₁, ← Category.assoc, spMap_comp_spMap_eq]
    obtain ⟨φ, hφ⟩ := exists_spMap_fac (ch.χ a) (spMap (ψ'.comp MvPolynomial.C) ≫ ch.χ a') (by
      rintro _ ⟨t, rfl⟩
      rw [e₁, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hy]
      exact hxa)
    obtain ⟨j, ψ, u, hψ, hu⟩ := hglue K a a' φ j' ψ' hφ
    have hc : ψ.comp (MvPolynomial.C.comp (g a)) = ψ'.comp (MvPolynomial.C.comp (g a')) := by
      have := congrArg (· ≫ s) hφ
      simp only [Category.assoc, hg, spMap_comp_spMap_eq] at this
      rw [← RingHom.comp_assoc, hψ]
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)
    have e : spMap ψ ≫ i (a, j) = spMap ψ' ≫ i (a', j') := by
      refine hP.hom_ext ?_ ?_
      · rw [← e₁, ← hφ, Category.assoc, h₁, ← Category.assoc, spMap_comp_spMap_eq, hψ]
      · obtain ⟨hv, e₂⟩ := h₂ (a, j)
        obtain ⟨hv', e₂'⟩ := h₂ (a', j')
        rw [Category.assoc, Category.assoc, e₂, e₂', ProjSpace.spMap_pt, ProjSpace.spMap_pt, hc]
        exact (ProjSpace.pt_eq_pt_iff _ _ _).2 ⟨u, hu⟩
    have t : Sp K := IsLocalRing.closedPoint K
    refine Set.mem_iUnion.2 ⟨j, spMap ψ t, ?_⟩
    rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply, hy]
  · rintro _ ⟨y, rfl⟩
    refine ⟨Set.mem_iUnion.2 ⟨_, y, rfl⟩, spMap MvPolynomial.C y, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h₁]

theorem exists_cellCl : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] (Z : Scheme.{0}) (s : Z ⟶ Sp O), IsProjOver s → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → Flat s → ∀ (ch : Charts Z) (g : ∀ a, O →+* ch.R a) (V J : Type) [Finite V] [Finite J] (N : ℕ) (ξ : ∀ a, J → Fin (N + 1) → MvPolynomial V (ch.R a)) (ℓ : ∀ a, J → Fin (N + 1) → ch.R a), (∀ a, ch.χ a ≫ s = spMap (g a)) → (∀ a, Cells (MvPolynomial.C : ch.R a →+* MvPolynomial V (ch.R a)) (ξ a) (ℓ a)) → (∀ (K : Type) [Field K] (a a' : ch.ι) (φ : ch.R a →+* K) (j' : J) (ψ' : MvPolynomial V (ch.R a') →+* K), spMap φ ≫ ch.χ a = spMap (ψ'.comp MvPolynomial.C) ≫ ch.χ a' → ∃ (j : J) (ψ : MvPolynomial V (ch.R a) →+* K) (u : Kˣ), ψ.comp MvPolynomial.C = φ ∧ ψ' ∘ ξ a' j' = (u : K) • (ψ ∘ ξ a j)) → ∃ (Z' : Scheme.{0}) (f : Z' ⟶ Z) (q : Z' ⟶ PSpace O N) (κ : ∀ a, J → (Sp (MvPolynomial V (ch.R a)) ⟶ Z')), CellCl s ch g ξ f q κ := by
  intro O _ _ _ Z s hproj hn hfl ch g V J _ _ N ξ ℓ hg hc hglue
  have hPp : IsProjOver (pullback.fst s (PSpace.str O N) ≫ s) :=
    ProjSpace.isProjOver_pullback hproj ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩
  have hP := IsPullback.of_hasPullback s (PSpace.str O N)
  generalize pullback.snd s (PSpace.str O N) = p₂ at hP
  generalize pullback.fst s (PSpace.str O N) = p₁ at hP hPp
  generalize pullback s (PSpace.str O N) = P at p₁ p₂ hP hPp
  have hv : ∀ a j, Ideal.span (Set.range (ξ a j)) = ⊤ := fun a j => by
    rw [Ideal.eq_top_iff_one, ← (hc a).one j]
    exact Ideal.sum_mem _ fun q _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨q, rfl⟩)
  let i : ∀ k : ch.ι × J, Sp (MvPolynomial V (ch.R k.1)) ⟶ P := fun k =>
    hP.lift (spMap MvPolynomial.C ≫ ch.χ k.1) (pt (MvPolynomial.C.comp (g k.1)) (ξ k.1 k.2) (hv _ _))
      (by rw [Category.assoc, hg, ProjSpace.pt_str, spMap_comp_spMap_eq])
  have h₁ : ∀ k, i k ≫ p₁ = spMap MvPolynomial.C ≫ ch.χ k.1 := fun k => hP.lift_fst _ _ _
  have h₂ : ∀ k, ∃ hv, i k ≫ p₂ = pt (MvPolynomial.C.comp (g k.1)) (ξ k.1 k.2) hv := fun k => ⟨_, hP.lift_snd _ _ _⟩
  have hmeet := iUnion_inter_chart hP ch g ξ hg hglue i h₁ h₂
  have hcell := fun a => GlobalTheory.GrCl.cells_immersed O Z P s N p₁ p₂ hP _ _ (ch.χ a) (g a) MvPolynomial.C J (ξ a) (ℓ a)
    (fun j => i (a, j)) inferInstance (hg a) (hc a) (fun j => h₁ (a, j)) (fun j => h₂ (a, j))
  have hnT := fun a => normal_sp_mvPolynomial hn (ch.χ a) V
  have hcar : IsOpen ch.carrier := isOpen_iUnion fun a => (ch.χ a).isOpenEmbedding.isOpen_range
  let Ω : P.Opens := ⟨p₁ ⁻¹' ch.carrier, hcar.preimage p₁.continuous⟩
  obtain ⟨U, j, e, hj, he, hej, hcov⟩ := GlobalTheory.ReducedUnion.exists_closed_union P (ch.ι × J)
    (fun k => Sp (MvPolynomial V (ch.R k.1))) i Ω (fun k => (hcell k.1).1 k.2)
    (fun k => by
      have := fun x => (hnT k.1 x).1
      exact isReduced_of_isReduced_stalk _)
    (fun k => by
      obtain ⟨W, hW⟩ := (hcell k.1).2.1 k.2
      refine ⟨p₁ ⁻¹ᵁ (ch.χ k.1).opensRange ⊓ W, ?_⟩
      rw [hW, ← hmeet, Set.inter_assoc]
      rfl)
    ⟨closure (⋃ k, Set.range (i k)), isClosed_closure, by
      refine Set.Subset.antisymm (Set.subset_inter subset_closure (Set.iUnion_subset fun k => ?_)) ?_
      · have : Set.range (i k) ⊆ ⋃ j, Set.range (i (k.1, j)) := Set.subset_iUnion (fun j => Set.range (i (k.1, j))) k.2
        rw [← hmeet] at this
        exact fun x hx => Set.mem_iUnion.2 ⟨k.1, (this hx).2⟩
      · rintro x ⟨hx, hxΩ⟩
        obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hxΩ
        obtain ⟨T, hT, eT⟩ := (hcell a).2.2
        have ho : IsOpen (p₁ ⁻¹' Set.range (ch.χ a)) := (ch.χ a).isOpenEmbedding.isOpen_range.preimage p₁.continuous
        have h3 := ho.closure_inter ⟨hx, ha⟩
        rw [hmeet, eT] at h3
        have h4 : x ∈ T ∩ p₁ ⁻¹' Set.range (ch.χ a) := ⟨closure_minimal Set.inter_subset_left hT h3, ha⟩
        rw [← eT, ← hmeet] at h4
        exact h4.1⟩
  have hcov' : ∀ x : U, ∃ k y, e k y = x := fun x => Set.mem_iUnion.1 (hcov.ge (Set.mem_univ x))
  have hnU : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme U := fun x => by
    obtain ⟨k, y, rfl⟩ := hcov' x
    exact (normal_stalk_iff (e k) y).2 (hnT k.1 y)
  have hfU : Flat (j ≫ Ω.ι ≫ p₁ ≫ s) := by
    have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat.{0})
    refine IsZariskiLocalAtSource.of_openCover (P := @Flat) (Scheme.Cover.mkOfCovers _ _ e hcov' he) fun k => ?_
    have := flat_spMap_C (ch.R k.1) V
    have e1 : e k ≫ j ≫ Ω.ι ≫ p₁ ≫ s = spMap MvPolynomial.C ≫ ch.χ k.1 ≫ s := by
      rw [← reassoc_of% h₁ k, ← hej k]
      simp only [Category.assoc]
    change Flat (e k ≫ j ≫ Ω.ι ≫ p₁ ≫ s)
    rw [e1]
    infer_instance
  obtain ⟨Z', ν, ε, hν, hnZ, hpZ, hfZ, hpb, hd⟩ :=
    GlobalTheory.GraphClosure.exists_normalisation_of_locallyClosed O P U (p₁ ≫ s) Ω j hPp hj hnU hfU
  have hε : IsOpenImmersion ε := MorphismProperty.of_isPullback hpb.flip inferInstance
  have hκ : ∀ k, (e k ≫ ε) ≫ ν = i k := fun k => by rw [Category.assoc, hpb.w, hej]
  have hr : Set.range ε = (ν ≫ p₁) ⁻¹' ch.carrier := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      have : ν (ε y) = Ω.ι (j y) := by rw [← Scheme.Hom.comp_apply, hpb.w, Scheme.Hom.comp_apply]
      change p₁ (ν (ε y)) ∈ ch.carrier
      rw [this]
      exact (j y).2
    · intro hx
      obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback hpb x ⟨ν x, hx⟩ rfl
      exact ⟨y, hy⟩
  refine ⟨Z', ν ≫ p₁, ν ≫ p₂, fun a l => e (a, l) ≫ ε, ?_, hnZ, ?_, ?_, fun a l => inferInstance, fun a l => ?_,
    fun a l => ?_, ?_, hr ▸ hd, fun K _ w w' hw e₁ e₂ => ?_, fun R K _ _ _ _ _ _ z y₀ y e₀ e₁ e₂ => ?_⟩
  · rwa [Category.assoc]
  · rwa [Category.assoc]
  · rw [Category.assoc, Category.assoc, hP.w]
  · rw [← Category.assoc, hκ, h₁]
  · rw [← Category.assoc, hκ]
    exact h₂ (a, l)
  · rw [← hr]
    refine Set.Subset.antisymm (Set.iUnion₂_subset ?_) ?_
    · rintro a l _ ⟨y, rfl⟩
      exact ⟨e (a, l) y, rfl⟩
    · rintro _ ⟨x, rfl⟩
      obtain ⟨⟨a, l⟩, y, rfl⟩ := hcov' x
      exact Set.mem_iUnion₂.2 ⟨a, l, y, rfl⟩
  · have key : ∀ v : Sp K ⟶ Z', Set.range (v ≫ ν ≫ p₁) ⊆ ch.carrier → ∃ v₀, v₀ ≫ ε = v := fun v hv =>
      ⟨IsOpenImmersion.lift ε v (by
        rintro _ ⟨t, rfl⟩
        rw [hr]
        exact hv ⟨t, rfl⟩), IsOpenImmersion.lift_fac _ _ _⟩
    have e₃ : w ≫ ν = w' ≫ ν := hP.hom_ext (by simpa only [Category.assoc] using e₁)
      (by simpa only [Category.assoc] using e₂)
    obtain ⟨v', rfl⟩ := key w' (e₁ ▸ hw)
    obtain ⟨v, rfl⟩ := key w hw
    rw [Category.assoc, Category.assoc, hpb.w] at e₃
    rw [(cancel_mono _).1 e₃]
  · obtain ⟨c, hc, -⟩ := (GlobalTheory.existsUnique_lift_spec_of_isLocalization (R' := K) (nonZeroDivisors R) le_rfl ν y
      (hP.lift z y₀ e₀.symm) (hP.hom_ext (by rw [Category.assoc, Category.assoc, hP.lift_fst, e₁])
        (by rw [Category.assoc, Category.assoc, hP.lift_snd, e₂]))).exists
    exact ⟨c, hc⟩

end GlobalTheory.GrCl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartFlagBaseHolds
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)
open GlobalTheory.LocM GlobalTheory.LocM.Cht
open MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocM.Cht.FlagBase

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem comp_listProd {B : Scheme.{0}} {G : Over B} [GrpObj G] {X Y : Over B} (e : X ⟶ Y) (L : List (Y ⟶ G)) :
    e ≫ L.prod = (L.map (e ≫ ·)).prod := by
  induction L with
  | nil => exact MonObj.comp_one e
  | cons a L ih => rw [List.prod_cons, MonObj.comp_mul, ih, List.map_cons, List.prod_cons]

theorem isCombAtG_bc {X : Scheme.{0}} (t : SAB H X) {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S')
    {x : Sp S ⟶ X} {m : ℕ} {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} {a : Fin m → S}
    {w : Sp (DualNumber S) ⟶ t.G.left} (h : IsCombAtG t x v a w) :
    IsCombAtG t (spMap ψ ≫ x) (fun j => spMap (dualMap ψ) ≫ v j) (fun j => ψ (a j)) (spMap (dualMap ψ) ≫ w) := by
  obtain ⟨u, hu, hw⟩ := h
  have he : spMap (dualMap ψ) ≫ (tEpsG x).hom = (tEpsG (spMap ψ ≫ x)).hom := by
    show spMap (dualMap ψ) ≫ spMap (algebraMap S (DualNumber S)) ≫ x =
      spMap (algebraMap S' (DualNumber S')) ≫ spMap ψ ≫ x
    rw [← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp]
    congr 2
    apply RingHom.ext
    intro r
    ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let e : tEpsG (spMap ψ ≫ x) ⟶ tEpsG x := Over.homMk (spMap (dualMap ψ)) he
  refine ⟨fun i => e ≫ u i, fun i => ?_, ?_⟩
  · show spMap (dualMap ψ) ≫ (u i).left = spMap (epsMul (ψ (a i))) ≫ spMap (dualMap ψ) ≫ v i
    rw [hu i, ← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp]
    congr 2
    apply RingHom.ext
    intro r
    ext <;> simp [dualMap, epsMul, _root_.mul_comm]
  · have hl : (List.ofFn fun i => e ≫ u i) = (List.ofFn u).map (e ≫ ·) := by
      rw [List.map_ofFn]
      rfl
    rw [hl, ← comp_listProd, Over.comp_left, hw]
    rfl

theorem bc_bc {Dw : Datum H} {X : Scheme.{0}} {t : SAB H X} {R S T : Type} [CommRing R] [CommRing S] [CommRing T]
    (φ : R →+* S) (ψ : S →+* T) (u : Vecs Dw t R) : (u.bc φ).bc ψ = u.bc (ψ.comp φ) := by
  funext τ i
  show spMap (dualMap ψ) ≫ spMap (dualMap φ) ≫ u τ i = spMap (dualMap (ψ.comp φ)) ≫ u τ i
  rw [← Category.assoc, ← spMap_comp]
  congr 2
  apply RingHom.ext
  intro r
  ext <;> simp [dualMap]

theorem exists_spMap_fromSpec {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {k : Type} [CommRing k]
    (w : Sp k ⟶ X) (h : Set.range w ⊆ (U : Set X)) : ∃ φ : Γ(X, U) →+* k, spMap φ ≫ hU.fromSpec = w := by
  have h' : Set.range w ⊆ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact h
  refine ⟨(Spec.preimage (IsOpenImmersion.lift hU.fromSpec w h')).hom, ?_⟩
  rw [spMap, CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]

theorem flagBase_of (hF : FrameBaseSt) : FlagBaseSt := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z k _ w
  refine ⟨fun hw => ?_, fun k' _ ψ u ⟨a, φ, hφ, hfr, hs⟩ => ?_⟩
  · have h0 : w (closedPoint k) ∈ ⋃ a, ((Z.U a).1 : Set Z.X) := Z.cover ▸ hw ⟨_, rfl⟩
    obtain ⟨a, ha⟩ := Set.mem_iUnion.1 h0
    obtain ⟨φ, hφ⟩ := exists_spMap_fromSpec (Z.U a).2 w (by
      rintro _ ⟨q, rfl⟩
      rwa [show q = closedPoint k from Subsingleton.elim (α := PrimeSpectrum k) _ _])
    have hφ' : spMap φ ≫ Z.chart a = w := hφ
    have hfr := hF _ _ _ _ _ _ _ _ _ _ _ φ _ (Z.frame a)
    rw [← Category.assoc, hφ'] at hfr
    refine ⟨(Z.fr a).bc φ, a, φ, hφ', hfr, fun τ n _ i hi => ⟨Pi.single i 1, fun j hj => ?_, ?_⟩⟩
    · exact Pi.single_eq_of_ne (fun e => by subst e; omega) _
    · exact isCombAtG_single _ _ (fun j => (hfr.1 τ j).1) i
  · refine ⟨a, ψ.comp φ, by rw [spMap_comp, Category.assoc, hφ], ?_, fun τ n hn i hi => ?_⟩
    · rw [Category.assoc, RingHom.comp_assoc]
      exact hF _ _ _ _ _ _ _ _ _ _ _ ψ _ hfr
    · obtain ⟨cf, h0, hc⟩ := hs τ n hn i hi
      refine ⟨fun j => ψ (cf j), fun j hj => (congrArg ψ (h0 j hj)).trans (map_zero ψ), ?_⟩
      rw [← bc_bc, Category.assoc]
      exact isCombAtG_bc _ ψ hc

theorem flagBase : FlagBaseSt := flagBase_of GlobalTheory.T.chart_frame_base_holds

end GlobalTheory.LocM.Cht.FlagBase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjGeneratorsMemFramePrimesTrueColumns
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.AtMember
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AtMember

set_option synthInstance.maxHeartbeats 400000 in

theorem conj_gen_mem_frame : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : Bl.ColW B f T) (Z : w.Lt) (t : Bl.ColT w Z), HalfAt (Formalism.L2.Herm.toErrXS t.full.1) (Fr.at (w.st Z) f) := by
  intro B f T w Z t k
  have hpi : (Formalism.L2.Herm.toErrXS t.full.1).piG = w.px.piG := by
    have h5 : (t.full.1.cols.levelZeroCompatibility (w.D Z).u₀).piG = (t.C.herm.levelZeroCompatibility (w.D Z).u₀).piG :=
      congrArg (fun X : Formalism.L2.Herm.ColsHermS (w.D Z) => (X.levelZeroCompatibility (w.D Z).u₀).piG) t.full.2
    exact h5.trans ((t.C.piG (w.D Z).u₀).symm.trans (t.std (w.D Z).u₀).gl.piG)
  show barE (w.D Z) ((Formalism.L2.Herm.toErrXS t.full.1).piG k) ∈
    Ideal.map (algebraMap (𝓞 (w.D Z).host.K) (𝓞 (w.D Z).host.E)) ((Fr.at (w.st Z) f).P.pb k).asIdeal
  rw [hpi]
  have hP : (Fr.at (w.st Z) f).P = w.I.C.P := by rw [w.C_eq]; rfl
  rw [hP]
  have hdiv := w.ok.pibar k
  set π : 𝓞 (w.D Z).host.E := w.px.piG k with hπdef
  set b : 𝓞 (w.D Z).host.E := barE (w.D Z) π with hbdef
  have hbc : ((b : 𝓞 (w.D Z).host.E) : (w.D Z).host.E) = (w.D Z).host.conj (π : (w.D Z).host.E) := barE_eq_conj _ _
  have hprod : π * b = (((w.D Z).host.g k : ℕ) : 𝓞 (w.D Z).host.E) := by
    apply RingOfIntegers.ext
    show ((π : (w.D Z).host.E) * (b : (w.D Z).host.E)) = algebraMap (𝓞 (w.D Z).host.E) (w.D Z).host.E (((w.D Z).host.g k : ℕ) : 𝓞 (w.D Z).host.E)
    rw [map_natCast, hbc]
    exact w.px.piG_norm k
  have hg0 : (((w.D Z).host.g k : ℕ) : 𝓞 (w.D Z).host.E) ≠ 0 := by
    intro h
    have h' := congrArg (algebraMap (𝓞 (w.D Z).host.E) (w.D Z).host.E) h
    rw [map_natCast, map_zero, Nat.cast_eq_zero] at h'
    exact ((w.D Z).host.g_prime k).ne_zero h'
  have hπ0 : π ≠ 0 := fun h => hg0 (by rw [← hprod, h, zero_mul])
  have hb0 : b ≠ 0 := fun h => hg0 (by rw [← hprod, h, mul_zero])
  have hbK : ((b : 𝓞 (w.D Z).host.E) : (w.D Z).host.E) ∈ (w.D Z).host.K := by
    have hπE : ((π : 𝓞 (w.D Z).host.E) : (w.D Z).host.E) ≠ 0 := fun h => hπ0 (RingOfIntegers.ext (h.trans (map_zero (algebraMap (𝓞 (w.D Z).host.E) (w.D Z).host.E)).symm))
    have e : ((b : 𝓞 (w.D Z).host.E) : (w.D Z).host.E) =
        ((w.D Z).host.g k : (w.D Z).host.E) / ((π : 𝓞 (w.D Z).host.E) : (w.D Z).host.E) := by
      rw [eq_div_iff hπE, mul_comm, hbc]
      exact w.px.piG_norm k
    rw [e]
    exact div_mem (natCast_mem _ _) (w.px.piG_K k)
  set y : 𝓞 (w.D Z).host.K := toOK b hbK with hydef
  have hy : algebraMap (𝓞 (w.D Z).host.K) (𝓞 (w.D Z).host.E) y = b := algebraMap_toOK b hbK
  rw [← hy]
  apply Ideal.mem_map_of_mem

  have iI : Algebra.IsIntegral (𝓞 (w.D Z).host.K) (𝓞 (w.D Z).host.E) :=
    ⟨fun x => (Algebra.IsIntegral.isIntegral (R := ℤ) x).tower_top⟩
  have hPk : ((w.I.C.P.pb k).asIdeal : Ideal (𝓞 (w.D Z).host.K)).IsPrime := (w.I.C.P.pb k).isPrime
  obtain ⟨Q, -, hQp, hQ⟩ := @Ideal.exists_ideal_over_prime_of_isIntegral (𝓞 (w.D Z).host.K) _ (𝓞 (w.D Z).host.E) _
    (algebraMap (𝓞 (w.D Z).host.K) (𝓞 (w.D Z).host.E)).toAlgebra iI
    ((w.I.C.P.pb k).asIdeal : Ideal (𝓞 (w.D Z).host.K)) hPk ⊥ (by
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_bot] at hx
      have : x = 0 := FaithfulSMul.algebraMap_injective (𝓞 (w.D Z).host.K) (𝓞 (w.D Z).host.E) (hx.trans (map_zero _).symm)
      rw [this]; exact Ideal.zero_mem _)
  have hgQ : π * b ∈ Q := by
    rw [hprod, ← map_natCast (algebraMap (𝓞 (w.D Z).host.K) (𝓞 (w.D Z).host.E)), ← Ideal.mem_comap, hQ]
    exact w.I.C.P.pb_over k
  rcases hQp.mem_or_mem hgQ with hπQ | hbQ
  ·
    have hQ'p : (Q.comap (barE (w.D Z) : 𝓞 (w.D Z).host.E →+* 𝓞 (w.D Z).host.E)).IsPrime := Ideal.comap_isPrime _ _
    have hbQ' : b ∈ Q.comap (barE (w.D Z) : 𝓞 (w.D Z).host.E →+* 𝓞 (w.D Z).host.E) := by
      rw [Ideal.mem_comap]
      show barE (w.D Z) (barE (w.D Z) π) ∈ Q
      rw [barE_barE]; exact hπQ
    let Q' : HeightOneSpectrum (𝓞 (w.D Z).host.E) :=
      ⟨Q.comap (barE (w.D Z) : 𝓞 (w.D Z).host.E →+* 𝓞 (w.D Z).host.E), hQ'p, fun h => hb0 (by rw [h] at hbQ'; exact (Ideal.mem_bot).1 hbQ')⟩
    have hmem : Q' ∈ (B.primes w.px).vG k := (Formalism.L2.Col.mem_divs hb0 Q').2 hbQ'
    have hd := (hdiv Q').1 hmem
    have hu : y ∈ (HeightOneSpectrum.under (𝓞 (w.D Z).host.K) Q').asIdeal := by
      show algebraMap (𝓞 (w.D Z).host.K) (𝓞 (w.D Z).host.E) y ∈ Q'.asIdeal
      rw [hy]; exact hbQ'
    have hd' : HeightOneSpectrum.under (𝓞 (w.D Z).host.K) Q' = w.I.C.P.pb k := hd
    rw [hd'] at hu
    exact hu
  · rw [← hQ]
    have h' : algebraMap (𝓞 (w.D Z).host.K) (𝓞 (w.D Z).host.E) y ∈ Q := hy.symm ▸ hbQ
    exact h'

end GlobalTheory.AtMember
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DerivativesSeparateLieBasisCoeffsCartesian
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
open MonoidalCategory CartesianMonoidalCategory MonObj

noncomputable section

namespace GlobalTheory.ArcLieCoord

attribute [local instance] Over.cartesianMonoidalCategory

theorem zeroPt_sc {S : Type} [CommRing S] (c : S) : GlobalTheory.PowLie.zeroPt S ≫ GlobalTheory.PowLie.sc c = GlobalTheory.PowLie.zeroPt S := by
  ext1
  simp only [Over.comp_left, GlobalTheory.PowLie.zeroPt, GlobalTheory.PowLie.sc, Over.homMk_left]
  rw [← spMap_comp]
  congr 1
  refine RingHom.ext fun r => ?_
  simp [epsScaleR]

theorem isTangent_prod {S : Type} [CommRing S] {G' : Over (Sp S)} [GrpObj G'] [IsCommMonObj G'] {n : ℕ}
    (v : Fin n → (epsR S ⟶ G')) (hv : ∀ k, IsTangent (v k)) (c : Fin n → S) :
    IsTangent (∏ k, GlobalTheory.PowLie.sc (c k) ≫ v k) := by
  rw [GlobalTheory.PowLie.isTangent_iff]
  have e := map_prod (ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom (G := G') (GlobalTheory.PowLie.zeroPt S)) (fun k => GlobalTheory.PowLie.sc (c k) ≫ v k) Finset.univ
  refine (e.trans ?_)
  refine (Finset.prod_eq_one fun k _ => ?_).trans rfl
  change GlobalTheory.PowLie.zeroPt S ≫ GlobalTheory.PowLie.sc (c k) ≫ v k = 1
  rw [← Category.assoc, zeroPt_sc, (GlobalTheory.PowLie.isTangent_iff _).1 (hv k)]
  rfl

theorem sep : ∀ {S : Type} [CommRing S] {X : Scheme.{0}} {x : Sp S ⟶ X} {G : Over X} {G' : Over (Sp S)} [GrpObj G] [GrpObj G'] [IsCommMonObj G'] {φ : G'.left ⟶ G.left}, IsGrpPullback G' G x φ → ∀ {n : ℕ} (v : Fin n → (epsR S ⟶ G')), IsLieBasis v → ∀ {V : G.left.Opens}, IsAffineOpen V → ⊤ ≤ ((η[G']).left ≫ φ) ⁻¹ᵁ V → ∀ (b : Fin n → S), (∀ f : Γ(G.left, V), ∑ k, b k * (valR ((v k).left ≫ φ) V f).snd = 0) → b = 0 := by
  intro S _ X x G G' _ _ _ φ h n v hv V hA hV b hb
  set w₀ : epsR S ⟶ G' := ∏ k, GlobalTheory.PowLie.sc (b k) ≫ v k with hw₀
  set w₁ : epsR S ⟶ G' := ∏ k, GlobalTheory.PowLie.sc ((0 : Fin n → S) k) ≫ v k with hw₁
  have c₀ : IsLieComb b v w₀ := (GlobalTheory.PowLie.isLieComb_iff_prod b v w₀).2 rfl
  have c₁ : IsLieComb 0 v w₁ := (GlobalTheory.PowLie.isLieComb_iff_prod 0 v w₁).2 rfl
  have t₀ : IsTangent w₀ := isTangent_prod v hv.1 b
  have t₁ : IsTangent w₁ := isTangent_prod v hv.1 0
  have l₀ := tan_le h w₀ t₀ V hV
  have l₁ := tan_le h w₁ t₁ V hV
  have fst_eq : ∀ (w : epsR S ⟶ G'), IsTangent w → ∀ f : Γ(G.left, V),
      (valR (w.left ≫ φ) V f).fst = valR ((η[G']).left ≫ φ) V f := by
    intro w hw f
    have e1 := GlobalTheory.HolHom.valR_spMap (TrivSqZeroExt.fstHom S S S).toRingHom (w.left ≫ φ) V (tan_le h w hw V hV) f
    have e2 : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w.left ≫ φ = (η[G']).left ≫ φ := by
      rw [← Category.assoc]
      exact congrArg (· ≫ φ) hw
    rw [e2] at e1
    rw [e1]
    rfl
  have e : w₀.left ≫ φ = w₁.left ≫ φ := by
    refine GlobalTheory.HolHom.point_ext hA l₀ l₁ fun f => ?_
    refine TrivSqZeroExt.ext ((fst_eq w₀ t₀ f).trans (fst_eq w₁ t₁ f).symm) ?_
    rw [comb_snd h v hv.1 b w₀ c₀ V hV f, comb_snd h v hv.1 0 w₁ c₁ V hV f, hb f]
    simp
  have hw : w₀ = w₁ := ReciprocityTheory.ChartRestriction.G.Chart.inj_over h e
  exact (hv.2 w₀ t₀).unique c₀ (hw ▸ c₁)

end GlobalTheory.ArcLieCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenDecompositionVectorBundle
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.LieMet GlobalTheory.Points GlobalTheory.GradedPieces GlobalTheory.LieVB GlobalTheory.VB

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.EigenFrames
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM sec_ext_of_cover)
open GlobalTheory.QCoh (appLinear appLinear_apply)
open GlobalTheory.LB (resG_resG le_iSup_inf)

variable {X : Scheme.{0}} {F G : X.Modules}

theorem isFrame_mkSec (N : Sub F) {U : X.Opens} {ν : Type} [Fintype ν] (e : ν → Γ(F, U))
    (he : ∀ i, e i ∈ N.sec U)
    (hli : ∀ (V : X.Opens) (h : V ≤ U), LinearIndependent Γ(X, V) fun i => resM F h (e i))
    (hsp : ∀ (V : X.Opens) (h : V ≤ U) (x : Γ(F, V)), x ∈ N.sec V →
      x ∈ Submodule.span Γ(X, V) (Set.range fun i => resM F h (e i))) :
    GlobalTheory.VB.IsFrame (F := N.toMod) fun i => N.mkSec (e i) (he i) := by
  rw [GlobalTheory.VB.isFrame_iff]
  intro V h
  have hcomp : (appLinear N.incl V) ∘ (fun i => resM N.toMod h (N.mkSec (e i) (he i))) =
      fun i => resM F h (e i) := funext fun i => by
    simp only [Function.comp, appLinear_apply]
    rw [app_resM]
    rfl
  refine ⟨LinearIndependent.of_comp (appLinear N.incl V) (hcomp ▸ hli V h), ?_⟩
  rintro y -
  have hx := hsp V h _ (N.incl_app_mem y)
  rw [← hcomp, Set.range_comp, Submodule.span_image] at hx
  obtain ⟨y', hy', e'⟩ := hx
  have : y' = y := N.incl_app_injective V (by rwa [appLinear_apply] at e')
  exact this ▸ hy'

section Frames

variable {O : Type} [CommRing O] (ρ : O →+* CategoryTheory.End F) {κ : Type} [Fintype κ]
  (τ : κ → (O →+* Γ(X, ⊤))) {m : κ → ℕ} {U : X.Opens} (B : (Σ i, Fin (m i)) → Γ(F, U))
  (hB : GlobalTheory.VB.IsFrame B)
  (hact : ∀ i k a, (act ρ a).app U (B ⟨i, k⟩) = resG X (le_top : U ≤ ⊤) (τ i a) • B ⟨i, k⟩)

end Frames

end GlobalTheory.EigenFrames
end
end


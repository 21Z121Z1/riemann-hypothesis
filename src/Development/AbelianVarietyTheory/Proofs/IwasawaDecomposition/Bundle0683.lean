import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0664
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0675
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0576
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineRefinementLieEmbedding
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb

theorem LeftInv.change {S : Type} [CommRing S] {M n m : ℕ} {D C : Fin m → Fin M → S} (h : LeftInv D C)
    {U : Fin n → Fin M → S} (a : Fin m → Fin n → S) (b : Fin n → Fin m → S) (hU : ∀ z, U z = ∑ j, b z j • C j)
    (hab : ∀ z z', ∑ j, a j z * b z' j = if z = z' then 1 else 0) :
    LeftInv (fun z => ∑ j, a j z • D j) U := by
  intro z z'
  have e : ∑ r, (∑ j, a j z • D j) r * U z' r = ∑ j, ∑ j', a j z * b z' j' * ∑ r, D j r * C j' r := by
    simp only [hU z', Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j' _ => Finset.sum_congr rfl fun r _ => by ring
  have h' : ∀ j j', ∑ r, D j r * C j' r = if j = j' then 1 else 0 := fun j j' => by convert h j j'
  rw [e]
  simp only [h', mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  convert hab z z'

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {L : FinLB X} {aff : ∀ i, IsAffineOpen (L.U i)} {M : ℕ} {crd : Crd t L M}

theorem IsLieEmb.exists_leftInv (h : IsLieEmb t L aff crd) (i : Fin L.n) {R : Type} [CommRing R]
    (φ : Γ(X, L.U i) →+* R) {x : Sp R ⟶ X} (hx : spMap φ ≫ (aff i).fromSpec = x) {n : ℕ} {u : Fin n → Tn t R}
    (hu : ∀ j, IsTanAtG t x (u j)) (hb : ∀ w, IsTanAtG t x w → ∃! a : Fin n → R, IsCombAtG t x u a w) :
    ∃ D : Fin n → Fin (M + 1) → R, LeftInv D fun z => crd i R φ (u z) := by
  obtain ⟨m, v, D, ⟨hv, hs⟩, hD⟩ := h.split i
  have hv' : ∀ j, IsTanAtG t x (spMap (dualMap φ) ≫ v j) := fun j => hx ▸ GlobalTheory.FactorDepth.isTanAtG_map t φ (hv j)
  have hC : ∀ j, crd i R φ (spMap (dualMap φ) ≫ v j) = φ ∘ crd i _ (RingHom.id _) (v j) := fun j =>
    h.nat i _ R (RingHom.id _) φ (v j) (by simpa [spMap] using hv j)
  choose a ha using fun j => (hb _ (hv' j)).exists
  choose b hb' using fun z => (hs R φ (u z) (hx ▸ hu z)).exists
  have ha' := fun j => (h.comb_iff i φ hx hu (hv' j) _).1 (ha j)
  have hb'' := fun z => (h.comb_iff i φ hx hv' (hu z) _).1 (hx ▸ hb' z)
  refine ⟨_, (hD.map φ).change a b (fun z => by simpa only [hC] using hb'' z) fun z z' => ?_⟩
  have e := (hb _ (hu z')).unique ((h.comb_iff i φ hx hu (hu z') fun z => ∑ j, a j z * b z' j).2 ?_)
    ((h.comb_iff i φ hx hu (hu z') fun z => if z = z' then 1 else 0).2 (by simp))
  · exact congrFun e z
  · rw [hb'' z']
    simp only [ha', Finset.smul_sum, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]

theorem IsLieEmb.exists_leftInv_let (h : IsLieEmb t L aff crd) (i : Fin L.n) {R : Type} [CommRing R]
    (φ : Γ(X, L.U i) →+* R) {x : Sp R ⟶ X} (hx : spMap φ ≫ (aff i).fromSpec = x) {Dw : Datum H} {e : Vecs Dw t R}
    {n : ℕ} (en : Fin n ≃ Let Dw.mult) (hu : ∀ τ j, IsTanAtG t x (e τ j))
    (hb : ∀ w, IsTanAtG t x w → ∃! a : Fin n → R, IsCombAtG t x (fun i => e (en i).1 (en i).2) a w) :
    ∃ D : Let Dw.mult → Fin (M + 1) → R, LeftInv D fun z => crd i R φ (e z.1 z.2) := by
  obtain ⟨D, hD⟩ := h.exists_leftInv i φ hx (fun i => hu (en i).1 (en i).2) hb
  refine ⟨fun z => D (en.symm z), fun z z' => ?_⟩
  obtain ⟨y, rfl⟩ := en.surjective z
  obtain ⟨y', rfl⟩ := en.surjective z'
  have := hD y y'
  simp only [Equiv.symm_apply_apply, EmbeddingLike.apply_eq_iff_eq]
  convert this

theorem tan_of_frame {Dw : Datum H} {l : Level H} {c : Coeff l} {R : Type} [CommRing R] {α : c.F →+* R} {x : Sp R ⟶ X}
    {e : Vecs Dw t R} (he : GlobalTheory.LocM.IsFrame t ((RingHom.id R).comp α) (spMap (RingHom.id R) ≫ x) (e.bc (RingHom.id R))) (τ) (j) :
    IsTanAtG t x (e τ j) := by
  have h1 : dualMap (RingHom.id R) = RingHom.id _ := RingHom.ext fun y => TrivSqZeroExt.inl_fst_add_inr_snd_eq y
  simpa [Vecs.bc, h1, spMap] using (he.1 τ j).1

theorem IsLieEmb.inBlock (h : IsLieEmb t L aff crd) {Dw : Datum H} {l : Level H} {c : Coeff l} {k : Type} [Field k]
    {R R' : Type} [CommRing R] [CommRing R'] {i i' : Fin L.n} (ρ : Γ(X, L.U i) →+* R) (ρ' : Γ(X, L.U i') →+* R')
    {x : Sp R ⟶ X} {x' : Sp R' ⟶ X} (hx : spMap ρ ≫ (aff i).fromSpec = x) (hx' : spMap ρ' ≫ (aff i').fromSpec = x')
    {e : Vecs Dw t R} {e' : Vecs Dw t R'} (ht : ∀ τ j, IsTanAtG t x (e τ j)) (ht' : ∀ τ j, IsTanAtG t x' (e' τ j))
    (φ : R →+* k) (φ' : R' →+* k) (hφ : spMap φ ≫ x = spMap φ' ≫ x') {α : c.F →+* k}
    (he : GlobalTheory.LocM.IsFrame t α (spMap φ ≫ x) (e.bc φ)) (he' : GlobalTheory.LocM.IsFrame t α (spMap φ' ≫ x') (e'.bc φ')) :
    InBlock (m := Dw.mult) (fun z => φ ∘ crd i R ρ (e z.1 z.2)) (fun z => φ' ∘ crd i' R' ρ' (e' z.1 z.2)) := by
  rintro ⟨τ, j⟩
  subst hx hx'
  have e1 : spMap (φ.comp ρ) ≫ (aff i).fromSpec = spMap φ ≫ spMap ρ ≫ (aff i).fromSpec := by
    rw [spMap_comp, Category.assoc]
  have e2 : spMap (φ'.comp ρ') ≫ (aff i').fromSpec = spMap φ' ≫ spMap ρ' ≫ (aff i').fromSpec := by
    rw [spMap_comp, Category.assoc]
  have hw := (he'.1 τ j).1
  obtain ⟨a, ha, -⟩ := he.2 τ (e'.bc φ' τ j) (hφ ▸ hw) (he'.1 τ j).2
  have h1 := (h.comb_iff i (φ.comp ρ) e1 (fun j => (he.1 τ j).1) (hφ ▸ hw) a).1 ha
  have h2 := h.trans i' i k (φ'.comp ρ') (φ.comp ρ) (e'.bc φ' τ j) (by rw [e1, e2, hφ]) (e2 ▸ hw)
  have h3 := h.nat i' R' k ρ' φ' (e' τ j) (ht' τ j)
  have h4 := fun j => h.nat i R k ρ φ (e τ j) (ht τ j)
  show φ' ∘ crd i' R' ρ' (e' τ j) ∈ _
  rw [← h3]
  refine h2 ▸ Submodule.smul_mem _ _ ?_
  rw [h1]
  exact Submodule.sum_mem _ fun j' _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j', (h4 j').symm⟩)

theorem noetherianSpace_model {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {p : ℕ}
    {W : ValuationSubring ℂ} (Y : Model Xo c (c.V W).subtype) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) :
    TopologicalSpace.NoetherianSpace Y.X := by
  have := c.fin
  have : NumberField c.F := {}
  have : IsDiscreteValuationRing (c.V W) := by
    refine (isDiscreteValuationRing_and_finite_residueField_of_numberField (c.V W) hp.ne_zero ?_).1
    rw [ValuationSubring.mem_nonunits_iff_or] at hW ⊢
    rcases hW with h | h
    · exact absurd (by exact_mod_cast h) hp.ne_zero
    · exact Or.inr fun h' => h (by simpa [Coeff.V] using h')
  have := projProper _ _ _ Y.proj
  have := LocallyOfFiniteType.isLocallyNoetherian Y.s
  have : CompactSpace Y.X := QuasiCompact.compactSpace_of_compactSpace Y.s
  have : AlgebraicGeometry.IsNoetherian Y.X := {}
  infer_instance

theorem exists_isFrameCover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ) (W : ValuationSubring ℂ) (Y : Model Xo c (c.V W).subtype), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (L : FinLB Y.X) (aff : ∀ i, IsAffineOpen (L.U i)) (M : ℕ) (crd : Crd Y.t L M), IsLieEmb Y.t L aff crd → ∃ (n : ℕ) (V : Fin n → Y.X.affineOpens) (ι : Fin n → Fin L.n) (ρ : ∀ b, Γ(Y.X, L.U (ι b)) →+* Γ(Y.X, (V b).1)) (α : ∀ b, c.F →+* Γ(Y.X, (V b).1)) (e : ∀ b, Vecs Dw Y.t Γ(Y.X, (V b).1)) (D : ∀ b, Let Dw.mult → Fin (M + 1) → Γ(Y.X, (V b).1)), IsFrameCover Y L aff crd V ι ρ α e D := by
  intro E _ _ _ H Dw l Xo c p W Y hp hW L aff M crd h
  have := noetherianSpace_model Y hp hW
  obtain ⟨-, hloc⟩ := GlobalTheory.T.exists_affine_eigenframe_near_image E H Dw l Xo c p W Y hp hW
  have hcov : ∀ x : Y.X, ∃ i, x ∈ L.U i := fun x =>
    TopologicalSpace.Opens.mem_iSup.1 ((L.isLB.cover).symm ▸ (TopologicalSpace.Opens.mem_top x))
  choose ι hι using hcov
  choose V α e n en hxV hVU hVj hs hfr hbas using fun x : Set.range Y.j => hloc x.1 (L.U (ι x.1)) (hι x.1) x.2
  obtain ⟨T, hT⟩ := (TopologicalSpace.NoetherianSpace.isCompact (Set.range Y.j)).elim_finite_subcover
    (fun x => ((V x).1 : Set Y.X)) (fun x => (V x).1.2) fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hxV _⟩
  have hρ : ∀ x, ∃ ρ : Γ(Y.X, L.U (ι x.1)) →+* Γ(Y.X, (V x).1),
      spMap ρ ≫ (aff (ι x.1)).fromSpec = (V x).2.fromSpec := fun x =>
    ⟨(Y.X.presheaf.map (homOfLE (hVU x)).op).hom, (aff (ι x.1)).map_fromSpec (V x).2 _⟩
  choose ρ hρ using hρ
  have htan : ∀ x τ j, IsTanAtG Y.t (V x).2.fromSpec (e x τ j) := fun x => tan_of_frame (hfr x _ (RingHom.id _))
  have hD : ∀ x, ∃ D : Let Dw.mult → Fin (M + 1) → Γ(Y.X, (V x).1),
      LeftInv D fun z => crd (ι x.1) _ (ρ x) (e x z.1 z.2) := fun x =>
    h.exists_leftInv_let (ι x.1) (ρ x) (hρ x) (en x) (htan x) (hbas x)
  choose D hD using hD
  obtain ⟨f, hf⟩ : ∃ f : Fin T.card → Set.range Y.j, ∀ x ∈ T, ∃ b, f b = x :=
    ⟨fun b => (T.equivFin.symm b).1, fun x hx => ⟨T.equivFin ⟨x, hx⟩, by simp⟩⟩
  refine ⟨T.card, fun b => V (f b), fun b => ι (f b).1, fun b => ρ (f b), fun b => α (f b), fun b => e (f b),
    fun b => D (f b), ?_, fun b => hρ _, fun b => hfr _, fun b => hs _, fun b => hD _,
    fun k _ b b' φ φ' hφ => ?_⟩
  · refine (Set.iUnion_subset fun b => hVj _).antisymm fun y hy => ?_
    obtain ⟨x, hx, hy'⟩ := Set.mem_iUnion₂.1 (hT hy)
    obtain ⟨b, rfl⟩ := hf x hx
    exact Set.mem_iUnion.2 ⟨b, hy'⟩
  · have hα : φ.comp (α (f b)) = φ'.comp (α (f b')) := by
      have e1 : spMap (φ.comp ((α (f b)).comp (c.V W).subtype)) =
          spMap (φ'.comp ((α (f b')).comp (c.V W).subtype)) := by
        rw [spMap_comp _ φ, spMap_comp _ φ', ← hs, ← hs, ← Category.assoc, ← Category.assoc]
        exact congrArg (· ≫ Y.s) hφ
      have e2 := congrArg CommRingCat.Hom.hom (Spec.map_injective e1)
      exact IsLocalization.ringHom_ext (nonZeroDivisors (c.V W)) e2
    exact h.inBlock (ρ _) (ρ _) (hρ _) (hρ _) (htan _) (htan _) φ φ' hφ (hfr _ k φ) (hα ▸ hfr _ k φ')

end GlobalTheory.FlagEmb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAnalyticLocalLatticeBasis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.Hor.LogCh

theorem IsLatFam.eventually_mem_of_graph {n g : ℕ} {K : (Fin n → ℂ) → Set (Fin g → ℂ)} {b₀ : Fin n → ℂ}
    {w₀ : Fin g → ℂ} {ζ : (Fin n → ℂ) → Fin g → ℂ} (hζ0 : ζ b₀ = w₀) (hζc : ContinuousAt ζ b₀)
    (hζ : ∀ᶠ q in 𝓝 (b₀, w₀), q.2 ∈ K q.1 ↔ q.2 = ζ q.1) : ∀ᶠ b in 𝓝 b₀, ζ b ∈ K b := by
  have ht : Filter.Tendsto (fun b => (b, ζ b)) (𝓝 b₀) (𝓝 (b₀, w₀)) := by
    have := (continuousAt_id.prodMk hζc).tendsto
    simpa [hζ0] using this
  filter_upwards [ht.eventually hζ] with b hb
  exact hb.2 rfl

theorem exists_isLatBasis_of_discrete {g : ℕ} (H : AddSubgroup (Fin g → ℂ))
    (hd : ∀ᶠ w in 𝓝 (0 : Fin g → ℂ), w ∈ H → w = 0)
    (hs : Submodule.span ℝ (H : Set (Fin g → ℂ)) = ⊤) :
    ∃ β : Fin (2 * g) → Fin g → ℂ, IsLatBasis (H : Set (Fin g → ℂ)) β := by
  set L : Submodule ℤ (Fin g → ℂ) := H.toIntSubmodule with hL
  have hLset : (L : Set (Fin g → ℂ)) = H := rfl
  haveI : DiscreteTopology L := by
    refine discreteTopology_of_isOpen_singleton_zero ?_
    obtain ⟨U, hU, hUo, h0U⟩ := eventually_nhds_iff.1 hd
    refine ⟨U, hUo, ?_⟩
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hx
      exact Subtype.ext (hU x.1 hx x.2)
    · rintro rfl
      exact h0U
  haveI : IsZLattice ℝ L := ⟨by rw [hLset]; exact hs⟩
  have hr : Module.finrank ℤ L = 2 * g := by
    rw [ZLattice.rank ℝ L, Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, mul_comm]
  let b := Module.finBasisOfFinrankEq ℤ L hr
  refine ⟨fun j => (b j : Fin g → ℂ), ?_, fun w => ⟨fun hw => ?_, ?_⟩⟩
  · have he : (fun j => (b j : Fin g → ℂ)) = ⇑(b.ofZLatticeBasis ℝ L) :=
      funext fun j => (Module.Basis.ofZLatticeBasis_apply ℝ L b j).symm
    rw [he]
    exact (b.ofZLatticeBasis ℝ L).linearIndependent
  · refine ⟨b.repr ⟨w, hw⟩, ?_⟩
    have h := congrArg (fun x : L => (x : Fin g → ℂ)) (b.sum_repr ⟨w, hw⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    exact h.symm
  · rintro ⟨m, rfl⟩
    exact H.sum_mem fun j _ => H.zsmul_mem (b j).2 _

theorem IsLatFam.eventually_intComb {n g r : ℕ} {B : Set (Fin n → ℂ)} {K : (Fin n → ℂ) → Set (Fin g → ℂ)}
    {b₀ : Fin n → ℂ} (hK : IsLatFam B K) (hb₀ : b₀ ∈ B) {lam : (Fin n → ℂ) → Fin r → Fin g → ℂ}
    (hlc : ContinuousAt lam b₀) (hlK : ∀ᶠ b in 𝓝 b₀, ∀ j, lam b j ∈ K b) (hβ : IsLatBasis (K b₀) (lam b₀))
    (y : Fin g → ℂ) :
    ∀ᶠ q in 𝓝 (b₀, y), q.2 ∈ K q.1 → ∃ m : Fin r → ℤ, q.2 = ∑ j, m j • lam q.1 j := by
  by_cases hy : y ∈ K b₀
  · obtain ⟨m, hm⟩ := (hβ.2 y).1 hy
    obtain ⟨ζ, hζ0, -, hζ⟩ := hK.2.2.2 b₀ hb₀ y hy
    set f : (Fin n → ℂ) → Fin g → ℂ := fun b => ∑ j, m j • lam b j with hf
    have hfc : ContinuousAt f b₀ := by
      have : Continuous (fun v : Fin r → Fin g → ℂ => ∑ j, m j • v j) := by fun_prop
      exact this.continuousAt.comp hlc
    have hf0 : f b₀ = y := hm.symm
    have hfK : ∀ᶠ b in 𝓝 b₀, f b ∈ K b := by
      filter_upwards [hlK, hK.1.mem_nhds hb₀] with b hb hbB
      obtain ⟨H, hH⟩ := hK.2.1 b hbB
      rw [← hH] at hb ⊢
      exact H.sum_mem fun j _ => H.zsmul_mem (hb j) _
    have ht : Filter.Tendsto (fun b => (b, f b)) (𝓝 b₀) (𝓝 (b₀, y)) := by
      have := (continuousAt_id.prodMk hfc).tendsto
      simpa [hf0] using this
    have hfζ : ∀ᶠ b in 𝓝 b₀, f b = ζ b := by
      filter_upwards [ht.eventually hζ, hfK] with b h1 h2
      exact h1.1 h2
    have hq : ∀ᶠ q : (Fin n → ℂ) × (Fin g → ℂ) in 𝓝 (b₀, y), f q.1 = ζ q.1 :=
      (continuous_fst.tendsto (b₀, y)).eventually hfζ
    filter_upwards [hq, hζ] with q h1 h2 h3
    exact ⟨m, (h2.1 h3).trans h1.symm⟩
  · have ho := hK.2.2.1.mem_nhds (show (b₀, y) ∈ {q : (Fin n → ℂ) × (Fin g → ℂ) | q.1 ∈ B ∧ q.2 ∉ K q.1} from ⟨hb₀, hy⟩)
    filter_upwards [ho] with q hq h
    exact absurd h hq.2

theorem isLatBasis_of_ball {g : ℕ} (H : AddSubgroup (Fin g → ℂ)) (lam : Fin (2 * g) → Fin g → ℂ) (R : ℝ)
    (hli : LinearIndependent ℝ lam) (hmem : ∀ j, lam j ∈ H) (hR : ∑ j, ‖lam j‖ ≤ R)
    (hball : ∀ w ∈ Metric.closedBall (0 : Fin g → ℂ) R, w ∈ H → ∃ m : Fin (2 * g) → ℤ, w = ∑ j, m j • lam j) :
    IsLatBasis (H : Set (Fin g → ℂ)) lam := by
  first
  | exact @_root_.GlobalTheory.LatticeBasisClosedBall.isLatBasis_of_closedBall
  | exact _root_.GlobalTheory.LatticeBasisClosedBall.isLatBasis_of_closedBall
  | (apply _root_.GlobalTheory.LatticeBasisClosedBall.isLatBasis_of_closedBall <;> assumption)
  | (intros; apply _root_.GlobalTheory.LatticeBasisClosedBall.isLatBasis_of_closedBall <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LatticeBasisClosedBall.isLatBasis_of_closedBall <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LatticeBasisClosedBall.isLatBasis_of_closedBall ..)

theorem IsLatFam.exists_analytic_locBasis : ∀ (n g : ℕ) (B : Set (Fin n → ℂ)) (K : (Fin n → ℂ) → Set (Fin g → ℂ))
    (b₀ : Fin n → ℂ), IsLatFam B K → b₀ ∈ B → Submodule.span ℝ (K b₀) = ⊤ →
    ∃ lam : (Fin n → ℂ) → Fin (2 * g) → Fin g → ℂ, AnalyticAt ℂ lam b₀ ∧ ∀ᶠ b in 𝓝 b₀, IsLatBasis (K b) (lam b) := by
  intro n g B K b₀ hK hb₀ hs
  obtain ⟨H₀, hH₀⟩ := hK.2.1 b₀ hb₀
  have h0 : (0 : Fin g → ℂ) ∈ K b₀ := by rw [← hH₀]; exact H₀.zero_mem
  obtain ⟨ζ₀, hζ₀0, -, hζ₀⟩ := hK.2.2.2 b₀ hb₀ 0 h0
  have hd : ∀ᶠ w in 𝓝 (0 : Fin g → ℂ), w ∈ H₀ → w = 0 := by
    have ht : Filter.Tendsto (fun w : Fin g → ℂ => (b₀, w)) (𝓝 0) (𝓝 (b₀, 0)) :=
      (continuous_const.prodMk continuous_id).continuousAt.tendsto
    filter_upwards [ht.eventually hζ₀] with w hw hwH
    have hwK : w ∈ K b₀ := by rw [← hH₀]; exact hwH
    rw [hw.1 hwK, hζ₀0]
  obtain ⟨β, hβ⟩ := exists_isLatBasis_of_discrete H₀ hd (by rw [hH₀]; exact hs)
  rw [hH₀] at hβ
  have hβK : ∀ j, β j ∈ K b₀ := fun j =>
    (hβ.2 (β j)).2 ⟨Pi.single j 1, by simp [Pi.single_apply]⟩
  choose ζ hζ0 hζa hζ using fun j => hK.2.2.2 b₀ hb₀ (β j) (hβK j)
  have hla : AnalyticAt ℂ (fun b j => ζ j b) b₀ := AnalyticAt.pi hζa
  have hlc := hla.continuousAt
  have hl0 : (fun j => ζ j b₀) = β := funext hζ0
  have hlK : ∀ᶠ b in 𝓝 b₀, ∀ j, ζ j b ∈ K b :=
    Filter.eventually_all.2 fun j => IsLatFam.eventually_mem_of_graph (hζ0 j) (hζa j).continuousAt (hζ j)
  have hβ' : IsLatBasis (K b₀) ((fun b j => ζ j b) b₀) := by
    show IsLatBasis (K b₀) (fun j => ζ j b₀)
    rw [hl0]; exact hβ
  set R : ℝ := ∑ j, (‖β j‖ + 1) with hR
  have hball := (isCompact_closedBall (0 : Fin g → ℂ) R).eventually_forall_of_forall_eventually (x₀ := b₀)
    (P := fun b w => w ∈ K b → ∃ m : Fin (2 * g) → ℤ, w = ∑ j, m j • ζ j b) fun y _ => IsLatFam.eventually_intComb hK hb₀ hlc hlK hβ' y
  have hli : ∀ᶠ b in 𝓝 b₀, LinearIndependent ℝ (fun j => ζ j b) := by
    have h1 : LinearIndependent ℝ ((fun b j => ζ j b) b₀) := hβ'.1
    exact hlc.tendsto.eventually h1.eventually
  have hnorm : ∀ᶠ b in 𝓝 b₀, ∀ j, ‖ζ j b‖ ≤ ‖β j‖ + 1 := by
    refine Filter.eventually_all.2 fun j => ?_
    have hc : ContinuousAt (fun b => ‖ζ j b‖) b₀ := (hζa j).continuousAt.norm
    have hlt : (fun b => ‖ζ j b‖) b₀ < (fun _ => ‖β j‖ + 1) b₀ := by simp [hζ0 j]
    filter_upwards [hc.eventually_lt continuousAt_const hlt] with b hb
    exact hb.le
  refine ⟨fun b j => ζ j b, hla, ?_⟩
  filter_upwards [hball, hli, hnorm, hlK, hK.1.mem_nhds hb₀] with b h1 h2 h3 h4 h5
  obtain ⟨H, hH⟩ := hK.2.1 b h5
  rw [← hH]
  refine isLatBasis_of_ball H _ R h2 (fun j => ?_) (Finset.sum_le_sum fun j _ => h3 j) fun w hw hwH => ?_
  · show ζ j b ∈ (H : Set (Fin g → ℂ)); rw [hH]; exact h4 j
  · exact h1 w hw (by rw [← hH]; exact hwH)

end GlobalTheory.ShFam.Hor.LogCh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArithmeticNefModelOfAmple
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.AmpleKaehler
open GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.Points

namespace GlobalTheory.AmpleModelPos

theorem isGenerated_tens {X : Scheme.{0}} {A B : LB X} (hA : IsGenerated A) (hB : IsGenerated B) :
    IsGenerated (tens A B) := by
  obtain ⟨a, s, hs⟩ := hA
  obtain ⟨b, t, ht⟩ := hB
  refine isGenerated_of_finite (fun q : Fin a × Fin b => EndOnTorsion.tensSec (s q.1) (t q.2))
    (top_le_iff.1 fun y _ => ?_)
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hs.ge (Set.mem_univ y))
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (ht.ge (Set.mem_univ y))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, j), (EndOnTorsion.nonzeroLocus_tensSec (s i) (t j)).ge ⟨hi, hj⟩⟩

section Pull

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D N : ℕ}

theorem semiPos_pull_fsO1 (f : Y ⟶ PSpace k N) (hf : f ≫ PSpace.str k N = p) (R : AnRead p σ D) :
    ((ProjAn.fsO1 k σ N).pull f hf).SemiPos R := by
  intro i c y hy ξ
  obtain ⟨j, rfl⟩ : ∃ j : Fin (N + 1), i = fun _ => j := ⟨i PUnit.unit, rfl⟩
  have hW : y ∈ ptsIn p σ (f ⁻¹ᵁ chart k N j) := mem_ptsIn.2 (Set.mem_iInter.1 (mem_ptsIn.1 hy.2) PUnit.unit)
  have ho := ChartGlue.isOpen_over (R.chart c).e (isOpen_ptsIn (p := p) (σ := σ) (f ⁻¹ᵁ chart k N j))
  have hn := ho.mem_nhds (ChartGlue.mem_over (R.chart c).e hy.1 hW)
  let g (a : Fin (N + 1)) : ReciprocityTheory.L2DbarEstimates.V D → ℂ :=
    ev p σ (f ⁻¹ᵁ chart k N j) (f.app _ (ratio k N j a)) ∘ (R.chart c).e.symm
  have hg (a) : ContDiffAt ℂ 2 (g a) ((R.chart c).e y) :=
    ((ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn D _ _ ho ((R.chart c).holo _ _)).contDiffAt hn).of_le
      (WithTop.coe_le_coe.2 le_top)
  have hj : g j ((R.chart c).e y) = 1 := by
    simp only [g, Function.comp_apply, (R.chart c).e.left_inv hy.1]
    have h1 : ratio k N j j = 1 := ratioOn_self
    rw [h1, map_one, ev_eq hW, map_one]
  have hpos : 0 < ∑ a, Complex.normSq (g a ((R.chart c).e y)) :=
    Finset.sum_pos' (fun a _ => Complex.normSq_nonneg _) ⟨j, Finset.mem_univ _, by rw [hj, map_one]; exact one_pos⟩
  have := ReciprocityTheory.L2DbarEstimates.leviV_log_sum_nonneg (u := fun a v => Complex.normSq (g a v))
    (fun a => ReciprocityTheory.L2DbarEstimates.contDiffAt_normSq_comp (hg a)) (fun a => ReciprocityTheory.L2DbarEstimates.logPshAt_normSq (hg a)) hpos ξ
  have e : (fun v => (((ProjAn.fsO1 k σ N).pull f hf).φ (fun _ => j) ((R.chart c).e.symm v) : ℂ)) =
      fun v => ((Real.log (∑ a, Complex.normSq (g a v)) : ℝ) : ℂ) := by
    funext v
    rw [ProjPos.fubiniStudy_weight_pullback_chart_formula]
    simp only [g, Function.comp_apply, Complex.normSq_eq_norm_sq]
  rw [e]
  exact this

end Pull

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

omit [NumberField F] in

theorem valR_ratio_baseChange {n : ℕ} (x : Sp ℂ ⟶ PSpace F n) (j a : Fin (n + 1)) :
    valR (x ≫ baseChange n (algebraMap (𝓞 F) F)) (chart (𝓞 F) n j) (ratio (𝓞 F) n j a) =
      valR x (chart F n j) (ratio F n j a) := by
  rw [valR_comp, ratio, baseChange_app_ratioOn]
  have key : ∀ (U : (PSpace F n).Opens) (hU : U = chart F n j) (hi : U ≤ chart F n j),
      valR x U (ratioOn U j hi a) = valR x (chart F n j) (ratio F n j a) := by
    rintro _ rfl _
    rfl
  exact key _ (baseChange_preimage_chart n _ j) _

omit [NumberField F] in

theorem pull_fsO1_ptMap (Z : TrueGeo.Model Y) (σ : F →+* ℂ) {n : ℕ} (f : Y.X ⟶ PSpace F n)
    (hf : f ≫ PSpace.str F n = Y.str) (g : Z.X ⟶ PSpace (𝓞 F) n) (hg : g ≫ PSpace.str (𝓞 F) n = Z.p)
    (h : Z.j ≫ g = f ≫ baseChange n (algebraMap (𝓞 F) F)) (j : PUnit → Fin (n + 1)) (y : Pts Y σ) :
    ((ProjAn.fsO1 (𝓞 F) (σ.comp (algebraMap (𝓞 F) F)) n).pull g hg).φ j (OfModel.ptMap Z σ y) =
      ((ProjAn.fsO1 F σ n).pull f hf).φ j y := by
  rw [show j = fun _ => j PUnit.unit from rfl, ProjPos.fubiniStudy_weight_pullback_chart_formula, ProjPos.fubiniStudy_weight_pullback_chart_formula]
  refine congrArg Real.log (Finset.sum_congr rfl fun a _ => ?_)
  change ‖valR ((y : Sp ℂ ⟶ Y.X) ≫ Z.j) _ _‖ ^ 2 = ‖valR (y : Sp ℂ ⟶ Y.X) _ _‖ ^ 2
  rw [← valR_comp, ← valR_comp, Category.assoc, h, ← Category.assoc, valR_ratio_baseChange]

theorem exists_model_strictPos : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (Δ : Y.Dv), Y.ample Δ →
    ∃ (q : ℕ+) (Z : TrueGeo.Model Y) (L : HermLB Z.p) (r : (L.B.pull Z.j).ι → Y.Fnˣ),
      Presents ((q : ℕ) • Δ) (L.B.pull Z.j) r ∧ ArInt.NefFib L ∧
        ∀ σ : F →+* ℂ, (pullW Z L σ).IsSmooth (Y.an σ) ∧ (pullW Z L σ).StrictPos (Y.an σ) := by
  intro F _ _ Y Δ hΔ
  have := CommonModel.isProper_of_isProjOver Y.isProjOver
  obtain ⟨e, he, he1⟩ := ((AmpleDominates.eventually_isGenerated Y.str hΔ Y.isAmple_projective_O_one.isLB).and
    (Filter.eventually_ge_atTop 1)).exists
  obtain ⟨b, sb, hsb⟩ := he.exists_fin_succ
  let α := algebraMap (𝓞 F) F
  let c := Y.str ≫ spMap α
  have hfa : (Y.ι ≫ baseChange Y.N α) ≫ PSpace.str (𝓞 F) Y.N = Y.str ≫ spMap α := by
    rw [Category.assoc, baseChange_str, ← Category.assoc]
    rfl
  obtain ⟨X, π, j, hX, hπ, hfl, H, ⟨ga, ha₁, ha₂⟩, gb, hb₁, hb₂⟩ :=
    IntModel.exists_flat_model_two (O := 𝓞 F) Y.str Y.isProjOver ⟨Y.N, 𝟙 _, inferInstance, Category.id_comp _⟩
      ⟨b, 𝟙 _, inferInstance, Category.id_comp _⟩ hfa (toProj_str c sb hsb)
  have := CommonModel.isProper_of_isProjOver hπ
  have hZ : Flat (spMap (Int.castRingHom (𝓞 F))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact (RingHom.flat_algebraMap_iff (R := ℤ) (S := 𝓞 F)).2 inferInstance
  have har : IsArithVar π Y.dim := ⟨inferInstance, inferInstance, hX, hπ, inferInstance,
    IntModel.topologicalKrullDim_eq_succ (RingOfIntegers.not_isField F) H Y.topologicalKrullDim_eq⟩
  let Z : TrueGeo.Model Y := ⟨X, π, har, j, H⟩
  let La : HermLB Z.p := (hermitianTwistingSheaf (𝓞 F) Y.N).pull ga ha₂
  let Lb : HermLB Z.p := (hermitianTwistingSheaf (𝓞 F) b).pull gb hb₂
  let L : HermLB Z.p := La.tens Lb
  let fb := toProj Y.str sb hsb
  have hfb : fb ≫ PSpace.str F b = Y.str := toProj_str _ _ _
  have hb₁' : Z.j ≫ gb = fb ≫ baseChange b α := hb₁.trans (toProj_baseChange α Y.str sb hsb).symm
  have hL : (L.B.pull Z.j).IsLB := LB.isLB_pull L.isLB Z.j
  have ea : pull Z.j (cls La.B La.isLB) = cls Y.O1 (LB.isLB_pull (O1_isLB F Y.N) Y.ι) := by
    have e₀ : cls La.B La.isLB = pull ga (cls _ (O1_isLB (𝓞 F) Y.N)) := cls_pull (O1_isLB (𝓞 F) Y.N) ga La.isLB
    rw [e₀, ← pull_comp, show Z.j ≫ ga = Y.ι ≫ baseChange Y.N α from ha₁,
      pull_comp, ← cls_pull (O1_isLB (𝓞 F) Y.N) _ (LB.isLB_pull (O1_isLB (𝓞 F) Y.N) _),
      (cls_eq_iff _ (O1_isLB F Y.N)).2 (lbIso_pull_O1 Y.N α), cls_pull (O1_isLB F Y.N)]
  have eb : pull Z.j (cls Lb.B Lb.isLB) = cls _ he.isLB := IntModel.pull_cls_O1 Z.j c he.isLB sb hsb gb hb₁ Lb.isLB
  obtain ⟨r, hr⟩ := IntModel.exists_presents (((⟨e, he1⟩ : ℕ+) : ℕ) • Δ) hL (by
    change toPic (e • Δ) = _
    have e₁ : cls L.B L.isLB = cls La.B La.isLB + cls Lb.B Lb.isLB := cls_tens La.isLB Lb.isLB L.isLB
    rw [cls_pull L.isLB Z.j hL, e₁, map_add, ea, eb,
      cls_div (isLB_lbPow (isLB_toLB Δ) e) (LB.isLB_pull (O1_isLB F Y.N) Y.ι), cls_lbPow (isLB_toLB Δ),
      map_nsmul, toPic_apply]
    abel)
  refine ⟨⟨e, he1⟩, Z, L, r, hr, OfLattice.nefFib_of_isGenerated har L
    (isGenerated_tens ((isGenerated_O1 _ _).pull ga) ((isGenerated_O1 _ _).pull gb)), fun σ => ?_⟩
  let ψa := (ProjAn.fsO1 F σ Y.N).pull Y.ι rfl
  let ψb := (ProjAn.fsO1 F σ b).pull fb hfb
  have sa : ψa.IsSmooth (Y.an σ) := ProjPos.fubiniStudy_weight_pullback_isSmooth _ _ _
  have pa : ψa.StrictPos (Y.an σ) := ProjPos.fubiniStudy_weight_pullback_closed_immersion_strictPos _ _ _
  have sb' : ψb.IsSmooth (Y.an σ) := ProjPos.fubiniStudy_weight_pullback_isSmooth _ _ _
  have pb : ψb.SemiPos (Y.an σ) := semiPos_pull_fsO1 _ _ _
  have eq (i : (L.B.pull Z.j).ι) (y : Pts Y σ) :
      (pullW Z L σ).φ i y = ψa.φ (i PUnit.unit).1 y + ψb.φ (i PUnit.unit).2 y := by
    rw [pullW_φ]
    exact congrArg₂ (· + ·) (pull_fsO1_ptMap Z σ Y.ι rfl ga ha₂ ha₁ _ y)
      (pull_fsO1_ptMap Z σ fb hfb gb hb₂ hb₁' _ y)
  have mem (i : (L.B.pull Z.j).ι) (y : Pts Y σ) (hy : y ∈ ptsIn Y.str σ ((L.B.pull Z.j).U i)) :
      y ∈ ptsIn Y.str σ (((O1 F Y.N).pull Y.ι).U (i PUnit.unit).1) ∧
        y ∈ ptsIn Y.str σ (((O1 F b).pull fb).U (i PUnit.unit).2) := by
    have h1 := mem_ptsIn_inf.1 (mem_of_mem_linComb (m := fun _ => OfModel.ptMap Z σ y) (fun _ => rfl) hy PUnit.unit)
    have ha := mem_ptsIn.1 (mem_of_mem_linComb (m := fun _ => PtsOver.map ga ha₂ _ (OfModel.ptMap Z σ y))
      (fun _ => rfl) h1.1 PUnit.unit)
    have hb := mem_ptsIn.1 (mem_of_mem_linComb (m := fun _ => PtsOver.map gb hb₂ _ (OfModel.ptMap Z σ y))
      (fun _ => rfl) h1.2 PUnit.unit)
    refine ⟨mem_ptsIn.2 (Set.mem_iInter.2 fun _ => ?_), mem_ptsIn.2 (Set.mem_iInter.2 fun _ => ?_)⟩
    · have e : ((y : Sp ℂ ⟶ Y.X) ≫ Z.j) ≫ ga = ((y : Sp ℂ ⟶ Y.X) ≫ Y.ι) ≫ baseChange Y.N α := by
        rw [Category.assoc, Category.assoc]
        exact congrArg _ ha₁
      have ha' := ha
      change (((y : Sp ℂ ⟶ Y.X) ≫ Z.j) ≫ ga).base (IsLocalRing.closedPoint ℂ) ∈
        chart (𝓞 F) Y.N ((i PUnit.unit).1 PUnit.unit) at ha'
      rw [e] at ha'
      have hm : ((y : Sp ℂ ⟶ Y.X) ≫ Y.ι).base (IsLocalRing.closedPoint ℂ) ∈
          chart F Y.N ((i PUnit.unit).1 PUnit.unit) := by
        exact (SetLike.ext_iff.1 (baseChange_preimage_chart Y.N α ((i PUnit.unit).1 PUnit.unit)) _).1 ha'
      exact hm
    · have e : ((y : Sp ℂ ⟶ Y.X) ≫ Z.j) ≫ gb = ((y : Sp ℂ ⟶ Y.X) ≫ fb) ≫ baseChange b α := by
        rw [Category.assoc, Category.assoc]
        exact congrArg _ hb₁'
      have hb' := hb
      change (((y : Sp ℂ ⟶ Y.X) ≫ Z.j) ≫ gb).base (IsLocalRing.closedPoint ℂ) ∈
        chart (𝓞 F) b ((i PUnit.unit).2 PUnit.unit) at hb'
      rw [e] at hb'
      have hm : ((y : Sp ℂ ⟶ Y.X) ≫ fb).base (IsLocalRing.closedPoint ℂ) ∈
          chart F b ((i PUnit.unit).2 PUnit.unit) := by
        exact (SetLike.ext_iff.1 (baseChange_preimage_chart b α ((i PUnit.unit).2 PUnit.unit)) _).1 hb'
      exact hm
  have hs : (pullW Z L σ).IsSmooth (Y.an σ) := by
    refine (Weight.isCInf_iff_isSmooth (Y.an σ)).1 fun i y hy => ?_
    obtain ⟨m1, m2⟩ := mem i y hy
    exact (((Weight.isCInf_iff_isSmooth (Y.an σ)).2 sa _ y m1).add
      ((Weight.isCInf_iff_isSmooth (Y.an σ)).2 sb' _ y m2)).congr (.of_forall fun z => eq i z)
  refine ⟨hs, fun i c y hy ξ hξ => ?_⟩
  obtain ⟨m1, m2⟩ := mem i y hy.2
  have e' : (pullW Z L σ).φ i = fun z => ψa.φ (i PUnit.unit).1 z + ψb.φ (i PUnit.unit).2 z := funext (eq i)
  show 0 < ((Y.an σ).chart c).levi ((pullW Z L σ).φ i) y ξ
  rw [e']
  refine lt_of_lt_of_eq ?_ (AlgChart.levi_add (sa.contDiffAt_two hy.1 m1) (sb'.contDiffAt_two hy.1 m2) ξ).symm
  exact add_pos_of_pos_of_nonneg (pa _ c y ⟨hy.1, m1⟩ ξ hξ) (pb _ c y ⟨hy.1, m2⟩ ξ)

end GlobalTheory.AmpleModelPos
end
end


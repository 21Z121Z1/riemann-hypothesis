import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle0007
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0067
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0055
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0002
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0059
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0058
import ReciprocityTheory.DualLattices.Bundle0005
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.Bundle0001
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0002
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0001
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0044
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0042
import ReciprocityTheory.DualLattices.Bundle0012
import ReciprocityTheory.DualLattices.Bundle0011
import ReciprocityTheory.DualLattices.Bundle0016
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0005
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0009
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FinConstFor

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsLocalBasis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.exists_local_basis' : ∀ (E : Type) [Field E] [NumberField E] (M : Type) [AddCommGroup M] [Module (𝓞 E) M] [Module.Finite (𝓞 E) M] [Module.IsTorsionFree (𝓞 E) M] (I : Type) [Fintype I] (ℓ : ℕ), ℓ.Prime → Fintype.card I = Module.finrank (𝓞 E) M → ∃ x : I → M, IsLocBasis (𝓞 E) ℓ x := by
  first | exact @PositivityTheory.Xgf.exists_local_basis' | exact PositivityTheory.Xgf.exists_local_basis'
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsLocalBasisCmOrderStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_basis_cm_order : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ℓ : ℕ), ℓ.Prime → ∃ (f : ℕ) (b : Fin f → 𝓞 E), 2 * f = Module.finrank ℚ E ∧ IsLocBasis (Algebra.adjoin ℤ {H.w0}) ℓ b := by
  first | exact @GlobalTheory.CompanionTheory.Relay.exists_local_basis_cm_order | exact GlobalTheory.CompanionTheory.Relay.exists_local_basis_cm_order | (intros; apply GlobalTheory.CompanionTheory.Relay.exists_local_basis_cm_order <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NormMapRestrictionCompatibleStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_map_restriction_compatible : ∀ {X Y : Scheme.{0}} (q : X ⟶ Y), IsFinite q → Flat q → LocallyOfFinitePresentation q → ∃ N : ∀ V : Y.Opens, Γ(X, q ⁻¹ᵁ V) →* Γ(Y, V), (∀ (V W : Y.Opens) (h : W ≤ V) (a : Γ(X, q ⁻¹ᵁ V)), (Y.presheaf.map (homOfLE h).op).hom (N V a) = N W ((X.presheaf.map (homOfLE (show q ⁻¹ᵁ W ≤ q ⁻¹ᵁ V from fun _ hx => h hx)).op).hom a)) ∧ ∀ (V : Y.Opens) (a : Γ(X, q ⁻¹ᵁ V)) (y : Y), y ∈ V → (y ∈ Y.basicOpen (N V a) ↔ ∀ x : X, q x = y → x ∈ X.basicOpen a) := by
  first | exact @GlobalTheory.CompanionTheory.FinFlatNorm.exists_norm_sheaf | exact GlobalTheory.CompanionTheory.FinFlatNorm.exists_norm_sheaf | (intros; apply GlobalTheory.CompanionTheory.FinFlatNorm.exists_norm_sheaf <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.OrbitAffineNeighbourhood
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot

noncomputable section
namespace GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd

variable {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X]

theorem mem_orbit_iff {x y : X.left} : y ∈ orbit G X x ↔
    ∃ z, (snd G X).left z = x ∧ (γ[G, X] : G ⊗ X ⟶ X).left z = y := by
  constructor
  · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩

theorem orbit_symm {x y : X.left} (h : y ∈ orbit G X x) : x ∈ orbit G X y := by
  obtain ⟨σ, -, h1, h2⟩ := GlobalTheory.T.shear_iso_action_projection G X
  obtain ⟨z, rfl, rfl⟩ := (mem_orbit_iff G X).1 h
  refine (mem_orbit_iff G X).2 ⟨σ.left z, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, h1]
  · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, h2]

theorem orbit_hom {x y : X.left} (h : y ∈ orbit G X x) : X.hom y = X.hom x := by
  obtain ⟨z, rfl, rfl⟩ := (mem_orbit_iff G X).1 h
  have e : (γ[G, X] : G ⊗ X ⟶ X).left ≫ X.hom = (snd G X).left ≫ X.hom := (Over.w _).trans (Over.w _).symm
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, e]

theorem stable_of_forall (V : X.left.Opens) (h : ∀ y ∈ V, orbit G X y ⊆ V) :
    (γ[G, X] : G ⊗ X ⟶ X).left ⁻¹ᵁ V = (snd G X).left ⁻¹ᵁ V := by
  ext z
  constructor
  · intro hz
    exact h _ hz (orbit_symm G X ((mem_orbit_iff G X).2 ⟨z, rfl, rfl⟩))
  · intro hz
    exact h _ hz ((mem_orbit_iff G X).2 ⟨z, rfl, rfl⟩)

variable {G X} in
theorem isFinite_snd (hG : IsFiniteLocallyFree G.hom) : IsFinite (snd G X).left := by
  have := hG.1
  have h : IsFinite (pullback.snd G.hom X.hom) := inferInstance
  exact h

variable {G X} in
theorem orbit_finite (hG : IsFiniteLocallyFree G.hom) (x : X.left) : (orbit G X x).Finite := by
  have := isFinite_snd (X := X) hG
  exact ((snd G X).left.finite_preimage_singleton x).image _

variable {G X} in
theorem isOpen_saturated (hG : IsFiniteLocallyFree G.hom) (O : X.left.Opens) :
    IsOpen {y : X.left | orbit G X y ⊆ O} := by
  have := isFinite_snd (X := X) hG
  have hc : IsClosed ((snd G X).left '' ((γ[G, X] : G ⊗ X ⟶ X).left ⁻¹' (O : Set X.left)ᶜ)) :=
    (snd G X).left.isClosedMap _ (O.isOpen.isClosed_compl.preimage (γ[G, X] : G ⊗ X ⟶ X).left.continuous)
  convert hc.isOpen_compl using 1
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_image, Set.mem_preimage, not_exists, not_and]
  constructor
  · intro h z hz hy
    exact hz (h ((mem_orbit_iff G X).2 ⟨z, hy, rfl⟩))
  · intro h w hw
    obtain ⟨z, hz, rfl⟩ := (mem_orbit_iff G X).1 hw
    by_contra hn
    exact h z hn hz

theorem mem_basicOpen_appLE' {P Y : Scheme.{0}} (c : P ⟶ Y) (U : Y.Opens) (hc : ⊤ ≤ c ⁻¹ᵁ U) (f : Γ(Y, U)) (z : P) :
    z ∈ P.basicOpen ((c.appLE U ⊤ hc).hom f) ↔ c z ∈ Y.basicOpen f := by
  have key : P.basicOpen ((c.appLE U ⊤ hc).hom f) = c ⁻¹ᵁ Y.basicOpen f := by
    rw [Scheme.preimage_basicOpen, Scheme.Hom.appLE, CommRingCat.comp_apply, Scheme.basicOpen_res, top_inf_eq]
  rw [key]
  rfl

theorem exists_norm {P D : Scheme.{0}} [IsAffine P] [IsAffine D] (v : P ⟶ D)
    (hv : FiniteFreeHom v.appTop.hom) (e : Γ(P, ⊤)) :
    ∃ N : Γ(D, ⊤), ∀ y : D, y ∈ D.basicOpen N ↔ ∀ z : P, v z = y → z ∈ P.basicOpen e := by
  letI := v.appTop.hom.toAlgebra
  have h1 : Module.Free Γ(D, ⊤) Γ(P, ⊤) := hv.1
  have h2 : Module.Finite Γ(D, ⊤) Γ(P, ⊤) := hv.2
  refine ⟨Algebra.norm Γ(D, ⊤) e, GlobalTheory.T.basic_open_norm_fibre_iff v _ e fun p => ?_⟩
  rw [GlobalTheory.T.norm_not_mem_prime_iff e p.asIdeal p.isPrime]
  constructor
  · intro h q hq
    exact h q.asIdeal q.isPrime hq
  · intro h q hq hq'
    exact h ⟨q, hq⟩ hq'

theorem exists_stable_affine_nbhd : ∀ {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X], IsFiniteLocallyFree G.hom → ∀ (x : X.left) (U : X.left.Opens), IsAffineOpen U → orbit G X x ⊆ U → ∃ (V : X.left.Opens) (W : S.Opens), x ∈ V ∧ IsAffineOpen V ∧ IsAffineOpen W ∧ V ≤ X.hom ⁻¹ᵁ W ∧ (γ[G, X] : G ⊗ X ⟶ X).left ⁻¹ᵁ V = (snd G X).left ⁻¹ᵁ V := by
  intro S G X _ _ hG x U hU hxU
  have hfl := hG.1
  have hfl2 := hG.2.1
  have hfl3 := hG.2.2
  obtain ⟨W, hsW, hW, hfree⟩ := GlobalTheory.T.finite_flat_locally_free_affine G.hom (X.hom x)
  have htrans : ∀ {y w : X.left}, y ∈ orbit G X x → w ∈ orbit G X y → w ∈ orbit G X x :=
    fun {y w} => GlobalTheory.T.mem_orbit_trans G X x y w
  let O : X.left.Opens := U ⊓ X.hom ⁻¹ᵁ W
  have hxO : orbit G X x ⊆ O := fun y hy => ⟨hxU hy, by
    show X.hom y ∈ W
    rw [orbit_hom G X hy]; exact hsW⟩
  let V₀ : X.left.Opens := ⟨{y | orbit G X y ⊆ O}, isOpen_saturated hG O⟩
  have hV₀O : V₀ ≤ O := fun y hy => hy (GlobalTheory.T.mem_orbit_self' G X y)
  have hV₀U : V₀ ≤ U := hV₀O.trans inf_le_left
  have hxV₀ : orbit G X x ⊆ V₀ := fun y hy w hw => hxO (htrans hy hw)
  obtain ⟨f, hKf, hfV⟩ := GlobalTheory.T.finite_set_basic_open_affine U V₀ hU hV₀U _ (orbit_finite hG x) hxV₀
  let D : X.left.Opens := X.left.basicOpen f
  have hD : IsAffineOpen D := hU.basicOpen f
  have hDW : D ≤ X.hom ⁻¹ᵁ W := (hfV.trans hV₀O).trans inf_le_right
  have hsq : IsPullback (fst G X).left (snd G X).left G.hom X.hom :=
    IsPullback.of_hasPullback G.hom X.hom
  obtain ⟨h, u, hpb⟩ := GlobalTheory.T.pullback_restrict_open hsq W D hDW
  have := isFinite_snd (X := X) hG
  haveI : IsAffine D.toScheme := hD
  haveI : IsAffine W.toScheme := hW
  haveI : IsAffine (G.hom ⁻¹ᵁ W).toScheme := hW.preimage G.hom
  haveI : IsAffine ((snd G X).left ⁻¹ᵁ D).toScheme := hD.preimage (snd G X).left
  have hfree' := GlobalTheory.T.finite_free_pullback_affine hpb hfree
  let P' : (G ⊗ X).left.Opens := (snd G X).left ⁻¹ᵁ D
  let c : P'.toScheme ⟶ X.left := P'.ι ≫ (γ[G, X] : G ⊗ X ⟶ X).left
  have hc : ⊤ ≤ c ⁻¹ᵁ U := by
    rintro z -
    have hz : (snd G X).left z.1 ∈ D := z.2
    have h1 : (γ[G, X] : G ⊗ X ⟶ X).left z.1 ∈ orbit G X ((snd G X).left z.1) :=
      (mem_orbit_iff G X).2 ⟨z.1, rfl, rfl⟩
    exact (hfV hz h1).1
  obtain ⟨N, hN⟩ := exists_norm ((snd G X).left ∣_ D) hfree' ((c.appLE U ⊤ hc).hom f)
  let V : X.left.Opens := D.ι ''ᵁ (D.toScheme.basicOpen N)
  have hVmem : ∀ y, y ∈ V ↔ y ∈ D ∧ orbit G X y ⊆ D := by
    intro y
    show y ∈ D.ι '' (D.toScheme.basicOpen N : Set D.toScheme) ↔ _
    constructor
    · rintro ⟨y', hy', rfl⟩
      refine ⟨y'.2, fun w hw => ?_⟩
      obtain ⟨z, hz, rfl⟩ := (mem_orbit_iff G X).1 hw
      have hzP : z ∈ P' := by
        show (snd G X).left z ∈ D
        rw [hz]; exact y'.2
      have h1 := (hN y').1 hy' ⟨z, hzP⟩ (Subtype.ext ((morphismRestrict_base_coe _ _ _).trans hz))
      exact (mem_basicOpen_appLE' c U hc f _).1 h1
    · rintro ⟨hyD, ho⟩
      refine ⟨⟨y, hyD⟩, (hN ⟨y, hyD⟩).2 fun z hz => ?_, rfl⟩
      refine (mem_basicOpen_appLE' c U hc f _).2 ?_
      have h2 : (snd G X).left z.1 = y :=
        (morphismRestrict_base_coe _ _ z).symm.trans (congrArg Subtype.val hz)
      exact ho ((mem_orbit_iff G X).2 ⟨z.1, h2, rfl⟩)
  refine ⟨V, W, (hVmem x).2 ⟨hKf (GlobalTheory.T.mem_orbit_self' G X x), fun y hy => hKf hy⟩, ?_, hW, ?_, ?_⟩
  · exact ((isAffineOpen_top D.toScheme).basicOpen N).image_of_isOpenImmersion D.ι
  · exact fun y hy => hDW ((hVmem y).1 hy).1
  · refine stable_of_forall G X V fun y hy w hw => (hVmem w).2 ⟨((hVmem y).1 hy).2 hw, fun t ht => ?_⟩
    exact ((hVmem y).1 hy).2 (GlobalTheory.T.mem_orbit_trans G X y w t hw ht)

end GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.OrdinaryCurveOfHodgeTate
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GR.OrdCurve

theorem nonempty_padicInt_hom (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (hc : IsAdicComplete (Ideal.span {(p : R)}) R) : Nonempty (ℤ_[p] →+* R) := by
  haveI := hc
  have hd : ∀ n : ℕ, ringChar (R ⧸ (Ideal.span {(p : R)}) ^ n) ∣ p ^ n := fun n => by
    apply ringChar.dvd
    rw [← map_natCast (Ideal.Quotient.mk ((Ideal.span {(p : R)}) ^ n)),
      Ideal.Quotient.eq_zero_iff_mem, Nat.cast_pow]
    exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n
  refine ⟨IsAdicComplete.liftRingHom (Ideal.span {(p : R)})
    (fun n => (ZMod.castHom (hd n) (R ⧸ (Ideal.span {(p : R)}) ^ n)).comp
      (PadicInt.toZModPow n)) ?_⟩
  intro m n hle
  rw [← PadicInt.zmod_cast_comp_toZModPow m n hle, ← RingHom.comp_assoc, ← RingHom.comp_assoc]
  congr 1
  exact RingHom.ext_zmod _ _

variable {R : Type} [CommRing R]

theorem isTorsPts_comp {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {p : ℕ} {N N' : Type}
    [AddCommGroup N] [AddCommGroup N'] {pt : N → (sp (R₀ := R) R ⟶ G)}
    (h : IsTorsPts G p pt) (e : N' ≃+ N) : IsTorsPts G p (fun x => pt (e x)) where
  inj := h.inj.comp e.injective
  add x y := by simpa using h.add (e x) (e y)
  range z := by
    rw [h.range z]
    exact ⟨fun ⟨x, hx⟩ => ⟨e.symm x, by simpa using hx⟩, fun ⟨x, hx⟩ => ⟨e x, hx⟩⟩

theorem torsFun_comp {C : Type} [Field C] [Algebra R C] {G : Over (Spec (CommRingCat.of R))}
    [GrpObj G] {p : ℕ} (T : TorsRep G p) {N N' : Type} [AddCommGroup N] [AddCommGroup N'] (pt : N → (sp (R₀ := R) R ⟶ G))
    (e : N' ≃+ N) :
    torsFun C T (fun x => pt (e x)) =
      (torsFun C T pt).map (LinearMap.funLeft R C (e : N' → N)) := by
  ext f
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨fun x => f (e.symm x), ⟨a, fun x φ h => ?_⟩, ?_⟩
    · exact ha (e.symm x) φ (by simpa using h)
    · ext x
      simp [LinearMap.funLeft_apply]
  · rintro ⟨g, ⟨a, ha⟩, rfl⟩
    exact ⟨a, fun x φ h => ha (e x) φ h⟩

theorem pt_zero {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {p : ℕ} {N : Type}
    [AddCommGroup N] {pt : N → (sp (R₀ := R) R ⟶ G)} (h : IsTorsPts G p pt) : pt 0 = 1 := by
  have := h.add 0 0
  rw [add_zero] at this
  exact left_eq_mul.mp this

theorem exists_far {p : ℕ} {C : Type} [Field C] [Algebra R C] {v : Valuation C NNReal}
    (hv : v.Integers R) {G : Over (Spec (CommRingCat.of R))} [GrpObj G] (T : TorsRep G p)
    {N : Type} [AddCommGroup N] {pt : N → (sp (R₀ := R) R ⟶ G)} (hpt : IsTorsPts G p pt)
    {z : sp (R₀ := R) R ⟶ G} (hz : z ^ p = 1)
    (hk : ∀ (k : Type) [Field k] [Algebra R k], spMap (Algebra.ofId R k) ≫ z ≠ 1) :
    ∃ t : N, ∃ g ∈ torsFun C T pt, v (g t - g 0) = 1 := by
  haveI : IsLocalRing R := isLocal_of_integers hv
  obtain ⟨t, rfl⟩ := (hpt.range z).1 hz
  have hex : ∀ x, ∃! φ : T.A →ₐ[R] R, spMap φ ≫ T.y = pt x := fun x =>
    T.univ R (pt x) ((hpt.range _).2 ⟨x, rfl⟩)
  choose φ hφ hφu using hex
  let k := IsLocalRing.ResidueField R
  have hne : (Algebra.ofId R k).comp (φ t) ≠ (Algebra.ofId R k).comp (φ 0) := by
    intro e
    apply hk k
    rw [← hφ t, ← Category.assoc, Chart.spMap_comp, e, ← Chart.spMap_comp, Category.assoc, hφ 0,
      pt_zero hpt]
    exact MonObj.comp_one _
  obtain ⟨a, ha⟩ : ∃ a, (Algebra.ofId R k) (φ t a) ≠ (Algebra.ofId R k) (φ 0 a) := by
    by_contra hcon
    push_neg at hcon
    exact hne (AlgHom.ext hcon)
  refine ⟨t, fun x => algebraMap R C (φ x a), ⟨a, fun x ψ h => ?_⟩, ?_⟩
  · rw [hφu x ψ h]
  · have hu : IsUnit (φ t a - φ 0 a) := by
      by_contra hn
      apply ha
      have hm : φ t a - φ 0 a ∈ IsLocalRing.maximalIdeal R := hn
      have := (Ideal.Quotient.eq_zero_iff_mem).2 hm
      rw [map_sub, sub_eq_zero] at this
      exact this
    rw [← map_sub]
    exact hv.one_of_isUnit hu

theorem exists_colen {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
    {v : Valuation C NNReal} [Algebra R C] [Algebra ℤ_[p] R] {cp : R}
    (hgp : PolarisedAFStatement) (hs : HodgeTateSetting p v R ℤ_[p] AlgEquiv.refl cp)
    (H : HodgeTateDatum p 1 v R ℤ_[p] AlgEquiv.refl cp) :
    ∃ cN, HasColen R v H.AA.carrier cN ∧ cN ^ 2 = v (p : C) ^ (p ^ 2) := by
  have hall := hgp p 1 C v R ℤ_[p] AlgEquiv.refl cp hs H
  dsimp only at hall
  obtain ⟨cA, cN, cO, -, hN, hO, -, hON⟩ := hall.2.2.2.2.2.2.2.2
  refine ⟨cN, hN, ?_⟩
  have hlen : HasLen v R (OmAA H.AA.carrier) (v (p : C)) := by
    refine ⟨1, fun _ => (p : R), ⟨?_⟩, by simp⟩
    exact (Submodule.quotEquivOfEq _ _ H.cotangent_ker_eq.symm).trans
      ((LinearMap.quotKerEquivOfSurjective H.φ H.cotangent_surjective).trans (PullbackHopfOrder.qPi p 1))
  have hc : cO = v (p : C) := hasLen_unique hs.integers hO hlen
  have hcard : Fintype.card (Nb p 1) = p ^ 2 := by
    simp [Nb, Ix, ZMod.card]
  rw [← hON, hc, hcard]

theorem reindex {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
    {v : Valuation C NNReal} [Algebra R C] [Algebra ℤ_[p] R] {cp : R}
    (hgp : PolarisedAFStatement) (hlt : v (p : C) < 1)
    (hs : HodgeTateSetting p v R ℤ_[p] AlgEquiv.refl cp)
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] (T : TorsRep G p) (g : ℕ) (hg : g = 1)
    (H : HodgeTateDatum p g v R ℤ_[p] AlgEquiv.refl cp) (pt : Nb p g → (sp (R₀ := R) R ⟶ G))
    (hpt : IsTorsPts G p pt) (hH : H.AA.carrier = torsFun C T pt)
    {z : sp (R₀ := R) R ⟶ G} (hz : z ^ p = 1)
    (hk : ∀ (k : Type) [Field k] [Algebra R k], spMap (Algebra.ofId R k) ≫ z ≠ 1) :
    ∃ pt' : ZMod p × ZMod p → (sp (R₀ := R) R ⟶ G), IsTorsPts G p pt' ∧ torsFun C T pt' =
      tens (Submodule.span R (Set.range fun (ψ : AddChar (ZMod p) C) (x : ZMod p) => ψ x))
        (intFun R (ZMod p)) := by
  subst hg
  obtain ⟨cN, hN, hcN⟩ := exists_colen hgp hs H
  have hfar : ∃ t : Nb p 1, ∃ f ∈ H.AA.carrier, v (f t - f 0) = 1 := by
    rw [hH]
    exact exists_far hs.integers T hpt hz hk
  have hcard : Fintype.card (Nb p 1) = p ^ 2 := by
    simp [Nb, Ix, ZMod.card]
  have hkill : ∀ x : Nb p 1, p • x = 0 := fun x => by
    ext i
    simp
  obtain ⟨e, he⟩ := GlobalTheory.T.order_p_squared_extremal_colength p C v R hs.integers hlt (Nb p 1) hkill hcard H.AA cN hN hcN hfar
  refine ⟨fun x => pt (e x), isTorsPts_comp hpt e, ?_⟩
  rw [torsFun_comp, ← hH, he]

end GlobalTheory.CompanionTheory.Ar.GR.OrdCurve

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem ordinaryCurve_of_hodgeTate : HodgeTateDatumStatement → OrdinaryCurveStatement := by
  intro hht p _ C _ _ _ v R _ _ hv hlt hc
  obtain ⟨f⟩ := OrdCurve.nonempty_padicInt_hom p R hc
  letI : Algebra ℤ_[p] R := f.toAlgebra
  obtain ⟨P, z, hg, hz, hk⟩ := GlobalTheory.T.polarised_abelian_variety_p_torsion p C v R hv hlt hc
  obtain ⟨⟨T⟩, cp, hs, H, pt, hpt, hH⟩ := hht p C v R hv hlt hc P
  obtain ⟨pt', h1, h2⟩ := OrdCurve.reindex GlobalTheory.T.polarised_augmentation_theorem hlt hs T P.g hg H pt hpt (hH T) hz hk
  exact ⟨P.A, P.grp, P.L, P.isAb, P.isLB, P.ample, T, pt', h1, h2⟩

end GlobalTheory.CompanionTheory.Ar.GR
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PadicEmbeddingValuationSubring
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_valuationSubring_of_padicEmbedding :
    ∀ (F : IntermediateField ℚ ℂ) (p : Nat.Primes) (κ : F →+* ℂ_[p]),
      ∃ W : ValuationSubring ℂ, ((p : ℕ) : ℂ) ∈ W.nonunits ∧
        ∀ x : F, ‖κ x‖ ≤ 1 ↔ (x : ℂ) ∈ W := by
  intro F p κ
  have hna : ∀ a b : ℂ_[p], ‖a + b‖ ≤ max ‖a‖ ‖b‖ := fun a b =>
    IsUltrametricDist.norm_add_le_max a b
  have hone : ‖κ 1‖ = 1 := by simp
  let A : Subring ℂ :=
    { carrier := {a | ∃ x : F, (x : ℂ) = a ∧ ‖κ x‖ ≤ 1}
      mul_mem' := by
        rintro _ _ ⟨x, rfl, hx⟩ ⟨y, rfl, hy⟩
        refine ⟨x * y, by simp, ?_⟩
        rw [map_mul, norm_mul]
        exact mul_le_one₀ hx (norm_nonneg _) hy
      one_mem' := ⟨1, by simp, by simp⟩
      add_mem' := by
        rintro _ _ ⟨x, rfl, hx⟩ ⟨y, rfl, hy⟩
        refine ⟨x + y, by simp, ?_⟩
        rw [map_add]
        exact (hna _ _).trans (max_le hx hy)
      zero_mem' := ⟨0, by simp, by simp⟩
      neg_mem' := by
        rintro _ ⟨x, rfl, hx⟩
        exact ⟨-x, by simp, by simpa using hx⟩ }
  let I : Ideal A :=
    { carrier := {a | ∃ x : F, (x : ℂ) = (a : ℂ) ∧ ‖κ x‖ < 1}
      add_mem' := by
        rintro a b ⟨x, hxa, hx⟩ ⟨y, hyb, hy⟩
        refine ⟨x + y, by simp [hxa, hyb], ?_⟩
        rw [map_add]
        exact (hna _ _).trans_lt (max_lt hx hy)
      zero_mem' := ⟨0, by simp, by simp⟩
      smul_mem' := by
        rintro ⟨c, z, hzc, hz⟩ a ⟨x, hxa, hx⟩
        refine ⟨z * x, by simp [hzc, hxa], ?_⟩
        rw [map_mul, norm_mul]
        calc ‖κ z‖ * ‖κ x‖ ≤ 1 * ‖κ x‖ := by gcongr
          _ < 1 := by simpa using hx }
  have hI : I ≠ ⊤ := by
    intro htop
    have h1 : (1 : A) ∈ I := by rw [htop]; trivial
    obtain ⟨x, hx1, hx⟩ := h1
    have hx1' : x = 1 := by
      apply Subtype.ext
      simpa using hx1
    rw [hx1', hone] at hx
    exact lt_irrefl _ hx
  obtain ⟨W, hAW, hIW⟩ := Ideal.image_subset_nonunits_valuationSubring I hI
  have key : ∀ x : F, ‖κ x‖ < 1 → (x : ℂ) ∈ W.nonunits := by
    intro x hx
    have hxA : (x : ℂ) ∈ A := ⟨x, rfl, hx.le⟩
    exact hIW ⟨⟨(x : ℂ), hxA⟩, ⟨x, rfl, hx⟩, rfl⟩
  refine ⟨W, ?_, fun x => ⟨fun hx => hAW ⟨x, rfl, hx⟩, fun hxW => ?_⟩⟩
  · have hnorm : ‖((p : ℕ) : ℂ_[p])‖ < 1 := by
      rw [← PadicComplex.coe_natCast, PadicComplex.norm_extends,
        ← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)), PadicAlgCl.norm_extends,
        Padic.norm_p]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast p.2.one_lt)
    have := key ((p : ℕ) : F) (by simpa using hnorm)
    simpa using this
  · by_contra hlt
    have hlt' : 1 < ‖κ x‖ := not_le.mp hlt
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hlt'
      linarith
    have hinv : ‖κ x⁻¹‖ < 1 := by
      rw [map_inv₀, norm_inv]
      exact inv_lt_one_of_one_lt₀ hlt'
    have hnu := key x⁻¹ hinv
    rw [ValuationSubring.mem_nonunits_iff] at hnu
    have hle : W.valuation (x : ℂ) ≤ 1 := (W.valuation_le_one_iff _).2 hxW
    have hprod : W.valuation (x : ℂ) * W.valuation ((x⁻¹ : F) : ℂ) = 1 := by
      rw [← map_mul]
      have : (x : ℂ) * ((x⁻¹ : F) : ℂ) = 1 := by
        have h0 : (x : ℂ) ≠ 0 := by simpa using hx0
        simp [h0]
      rw [this, map_one]
    have : W.valuation (x : ℂ) * W.valuation ((x⁻¹ : F) : ℂ) < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_left' hle) hnu
    exact absurd hprod this.ne

end GlobalTheory.CompanionTheory.Ar.Flat
end


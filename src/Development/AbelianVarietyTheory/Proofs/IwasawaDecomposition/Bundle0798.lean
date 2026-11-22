import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0571
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0660
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0792
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0741
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0629
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0664
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0782
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0726
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0736
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0745
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0766
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0783
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GeometricWeakTiesOfStrong
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0698
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0784
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0663
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0019
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0750
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0810
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0818
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0819
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0775
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0684
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0265
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0266
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0033
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0524
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0633
import Development.AutomorphicArithmetic.SemilinearForms.GeoExtFW
import Development.AutomorphicArithmetic.SemilinearForms.GeoExtOm
import Development.AutomorphicArithmetic.SemilinearForms.GeoExtTies
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0730

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHomogeneousPolysTangentBasis
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj

namespace GlobalTheory.LineNorm.WedgeMax

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_poly (A A' : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CharZero A] [CommRing A']
    [IsDomain A'] [Algebra A A'] [Module.Finite A A'] (hinj : Function.Injective (algebraMap A A')) (g k : ℕ)
    (J : Type) [Fintype J] (h : J → Fin g → A') (c : ℕ) (hc : c ≠ 0) (hh : ∀ i, ∃ j, h j = Pi.single i (c : A')) :
    ∃ (d : ℕ+) (n : ℕ) (B : Fin n → MvPolynomial (Fin k → Fin g) A), (∀ i, (B i).IsHomogeneous d) ∧
      (∀ s, ∃ (i : Fin n) (c : ℕ), c ≠ 0 ∧
        B i = MvPolynomial.C (c : A) * (MvPolynomial.X s : MvPolynomial (Fin k → Fin g) A) ^ (d : ℕ)) ∧
      ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] (x : A →+* C)
        (m : ℕ) (hk : k ≤ m) (a : Fin m → Fin g → C), LinearIndependent C a → ∀ N : Fin m → ℝ,
        (∀ x' : A' →+* C, x'.comp (algebraMap A A') = x → ∀ l, N l = sInf {r | ∃ cf : Fin m → C, cf l ≠ 0 ∧
          (∀ l', l < l' → cf l' = 0) ∧ (∀ j, ‖∑ i, x' (h j i) * ∑ l', cf l' * a l' i‖ ≤ 1) ∧ r = ‖cf l‖⁻¹}) →
        ((d : ℕ) : ℝ) * ∑ l : Fin k, Real.log (N (Fin.castLE hk l)) =
          Real.log (⨆ i, ‖MvPolynomial.eval₂ x (minor a hk) (B i)‖) := by
  classical
  obtain ⟨d, n, B, hB, hN⟩ := GlobalTheory.T.exists_homogeneous_invariants_norms A A' hinj (Fin k → Fin g) (Fin k → J) fun σ s => ∏ i, h (σ i) (s i)
  let e := Fintype.equivFin (Fin n ⊕ (Fin k → Fin g))
  let B' : Fin n ⊕ (Fin k → Fin g) → MvPolynomial (Fin k → Fin g) A :=
    Sum.elim B fun s => MvPolynomial.C (((c ^ k) ^ (d : ℕ) : ℕ) : A) * MvPolynomial.X s ^ (d : ℕ)
  refine ⟨d, _, fun i => B' (e.symm i), fun i => ?_,
    fun s => ⟨e (Sum.inr s), (c ^ k) ^ (d : ℕ), pow_ne_zero _ (pow_ne_zero _ hc), by simp [B']⟩, ?_⟩
  · show (B' (e.symm i)).IsHomogeneous d
    rcases e.symm i with i | s
    · exact hB i
    · exact (MvPolynomial.isHomogeneous_X_pow s _).C_mul _
  intro C _ _ _ _ x m hk a ha N hx
  obtain ⟨x', hx'⟩ : ∃ x' : A' →+* C, x'.comp (algebraMap A A') = x := by
    by_contra h0
    have h1 := (hN C x (minor a hk) 0 fun y hy => absurd ⟨y, hy⟩ h0).trans
      (hN C x (minor a hk) 1 fun y hy => absurd ⟨y, hy⟩ h0).symm
    simp at h1
  have cov := fun (y : A' →+* C) (hy : y.comp (algebraMap A A') = x) =>
    GlobalTheory.T.successive_minima_positive_norms C g J (fun j i => y (h j i)) (fun b hb => funext fun i => by
      obtain ⟨j, hj⟩ := hh i
      have := hb j
      rw [Finset.sum_eq_single i (fun i' _ hi => by simp [hj, Pi.single_eq_of_ne hi]) (by simp)] at this
      simpa [hj, hc] using this) m a ha N (hx y hy)
  have hP := hN C x (minor a hk) (∏ l : Fin k, N (Fin.castLE hk l)) fun y hy => by
    simp only [map_prod]
    exact ((cov y hy).2 k hk).symm
  have hpos := (cov x' hx').1
  have hP0 : 0 ≤ ∏ l : Fin k, N (Fin.castLE hk l) := Finset.prod_nonneg fun l _ => (hpos _).le
  rw [← Real.log_prod fun l _ => (hpos _).ne', ← Real.log_pow,
    e.symm.iSup_comp (g := fun i => ‖MvPolynomial.eval₂ x (minor a hk) (B' i)‖)]
  congr 1
  refine le_antisymm ?_ (Real.iSup_le ?_ (pow_nonneg hP0 _))
  · rw [hP]
    exact Real.iSup_le (fun i => le_ciSup (f := fun i => ‖MvPolynomial.eval₂ x (minor a hk) (B' i)‖)
      (Finite.bddAbove_range _) (Sum.inl i)) (Real.iSup_nonneg fun _ => norm_nonneg _)
  · rintro (i | s)
    · rw [hP]
      exact le_ciSup (f := fun i => ‖MvPolynomial.eval₂ x (minor a hk) (B i)‖) (Finite.bddAbove_range _) i
    · have e1 : ‖MvPolynomial.eval₂ x (minor a hk) (B' (Sum.inr s))‖ = ‖(c : C) ^ k * minor a hk s‖ ^ (d : ℕ) := by
        simp [B', mul_pow]
      rw [e1]
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
      choose j hj using hh
      rw [(cov x' hx').2 k hk]
      refine le_trans (le_of_eq ?_) (le_ciSup (Finite.bddAbove_range _) fun i => j (s i))
      rw [Finset.sum_eq_single s (fun s' _ hs => ?_) (by simp)]
      · simp [hj]
      · obtain ⟨i, hi⟩ := Function.ne_iff.1 hs
        rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hj, Pi.single_eq_of_ne hi]), zero_mul]

theorem spMap_comp {S T U : Type} [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) :
    spMap (ψ.comp φ) = spMap ψ ≫ spMap φ := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem spMap_dual_comp {S T U : Type} [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) :
    spMap (dualMap (ψ.comp φ)) = spMap (dualMap ψ) ≫ spMap (dualMap φ) := by
  rw [← spMap_comp]
  congr 1
  exact RingHom.ext fun x => by ext <;> simp [dualMap]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

theorem isTanBasis_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {x : Sp R ⟶ X} {g : ℕ}
    {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)} (he : IsTanBasis t x e) :
    IsTanBasis t (spMap φ ≫ x) fun i => spMap (dualMap φ) ≫ e i := by
  refine ⟨fun i => GlobalTheory.LieMet.isTan_map φ rfl (he.1 i), fun T _ ψ w => ?_⟩
  have := he.2 T (ψ.comp φ) w
  simpa only [spMap_comp, spMap_dual_comp, Category.assoc] using this

theorem exists_comb {S : Type} [CommRing S] {x : Sp S ⟶ X} {m : ℕ} {u : Fin m → (Sp (DualNumber S) ⟶ t.G.left)}
    (hu : ∀ l, IsTanAtG t x (u l)) (cf : Fin m → S) : ∃ w, IsTanAtG t x w ∧ IsCombAtG t x u cf w :=
  ⟨_, GlobalTheory.LieMet.isTan_tv (∑ l, cf l • GlobalTheory.LieMet.tanOf (hu l)),
    (GlobalTheory.LieMet.isComb_iff (fun l => GlobalTheory.LieMet.tanOf (hu l)) cf _).2 rfl⟩

theorem comb_unique {S : Type} [CommRing S] {x : Sp S ⟶ X} {m : ℕ} {u : Fin m → (Sp (DualNumber S) ⟶ t.G.left)}
    (hu : ∀ l, IsTanAtG t x (u l)) {cf : Fin m → S} {w w' : Sp (DualNumber S) ⟶ t.G.left}
    (h : IsCombAtG t x u cf w) (h' : IsCombAtG t x u cf w') : w = w' :=
  ((isCombAtG_iff t _ (fun j => ovT (hu j)) _ _).1 h).symm.trans ((isCombAtG_iff t _ (fun j => ovT (hu j)) _ _).1 h')

variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]

omit [IsUltrametricDist C] in

theorem grNorm_eq {x : Sp C ⟶ X} {g m : ℕ} {e : Fin g → (Sp (DualNumber C) ⟶ t.G.left)} (he : ∀ i, IsTanAtG t x (e i))
    {Λ : Set (Sp (DualNumber C) ⟶ t.G.left)} {P : (Fin g → C) → Prop}
    (hΛ : ∀ b w, IsCombAtG t x e b w → (w ∈ Λ ↔ P b)) {u : Fin m → (Sp (DualNumber C) ⟶ t.G.left)}
    {a : Fin m → Fin g → C} (hu : ∀ l, IsCombAtG t x e (a l) (u l)) (l : Fin m) :
    GlobalTheory.ShFam.Pad.grNorm t x Λ u l = sInf {r | ∃ cf : Fin m → C, cf l ≠ 0 ∧ (∀ l', l < l' → cf l' = 0) ∧
      P (fun i => ∑ l', cf l' * a l' i) ∧ r = ‖cf l‖⁻¹} := by
  have hut : ∀ l, IsTanAtG t x (u l) := fun l => by
    obtain ⟨w, hw, hw'⟩ := exists_comb t he (a l)
    exact comb_unique t he hw' (hu l) ▸ hw
  have key : ∀ cf w, IsCombAtG t x u cf w → (w ∈ Λ ↔ P fun i => ∑ l', cf l' * a l' i) := fun cf w hw => by
    refine hΛ _ w ?_
    have := tanLinG e he u (Matrix.of fun i l => a l i) cf w hu hw
    convert this using 2 with i
    simp [Matrix.mulVec, dotProduct, mul_comm]
  unfold GlobalTheory.ShFam.Pad.grNorm
  congr 1
  ext r
  refine exists_congr fun cf => and_congr_right fun _ => and_congr_right fun _ => and_congr_left fun _ => ?_
  refine ⟨fun ⟨w, h1, h2⟩ => (key cf w h2).1 h1, fun hP => ?_⟩
  obtain ⟨w, -, hw⟩ := exists_comb t hut cf
  exact ⟨w, (key cf w hw).2 hP, hw⟩

theorem ext_intO (hX : X.IsSeparated) (x x' : Sp ↥(intO C) ⟶ X)
    (h : spMap (intO C).subtype ≫ x' = spMap (intO C).subtype ≫ x) : x' = x := by
  have : IsDominant (spMap (intO C).subtype) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
    intro z hz
    have : z = 0 := Subtype.ext hz
    simp [this])⟩
  exact ext_of_isDominant (spMap (intO C).subtype) h

theorem mem_latDR (hX : X.IsSeparated) {x : Sp ↥(intO C) ⟶ X} {g : ℕ}
    {e : Fin g → (Sp (DualNumber ↥(intO C)) ⟶ t.G.left)} (he : IsTanBasis t x e) (b : Fin g → C)
    (w : Sp (DualNumber C) ⟶ t.G.left)
    (hw : IsCombAtG t (spMap (intO C).subtype ≫ x) (fun i => spMap (dualMap (intO C).subtype) ≫ e i) b w) :
    w ∈ latDR t (spMap (intO C).subtype ≫ x) ↔ ∀ i, ‖b i‖ ≤ 1 := by
  have h1 : spMap (RingHom.id ↥(intO C)) = 𝟙 _ := Spec.map_id _
  have h2 : dualMap (RingHom.id ↥(intO C)) = RingHom.id _ := by
    refine RingHom.ext fun z => ?_
    ext <;> simp [dualMap]
  have h3 : spMap (dualMap (RingHom.id ↥(intO C))) = 𝟙 _ := by rw [h2]; exact Spec.map_id _
  have hD0 := he.2 _ (RingHom.id ↥(intO C))
  simp only [h1, h3, Category.id_comp] at hD0
  have hDk := (isTanBasis_map t (intO C).subtype he).1
  refine ⟨?_, fun hc => ?_⟩
  · rintro ⟨xO', hx, vO, hv, rfl⟩
    obtain rfl := ext_intO hX _ xO' hx
    obtain ⟨a, ha, -⟩ := hD0 vO hv
    have e := (he.2 C _ _ (GlobalTheory.LieMet.isTan_map (intO C).subtype rfl hv)).unique hw
      (GlobalTheory.LatDRFree.comb_map t (intO C).subtype ha)
    intro i
    rw [e]
    exact (a i).2
  · obtain ⟨v, hv, ha⟩ := exists_comb t he.1 fun i => (⟨b i, hc i⟩ : ↥(intO C))
    exact ⟨x, rfl, v, hv, comb_unique t hDk (GlobalTheory.LatDRFree.comb_map t (intO C).subtype ha) hw⟩

theorem norm_le_one {A A' : Type} [CommRing A] [CommRing A'] [Algebra A A'] [Module.Finite A A'] (x' : A' →+* C)
    (hx : ∀ a, ‖x' (algebraMap A A' a)‖ ≤ 1) (b : A') : ‖x' b‖ ≤ 1 := by
  have hi : ∀ z : C, z ∈ (NormedField.valuation (K := C)).integer ↔ ‖z‖ ≤ 1 := fun z => by
    rw [Valuation.mem_integer_iff, NormedField.valuation_apply]
    exact_mod_cast Iff.rfl
  let y : A →+* (NormedField.valuation (K := C)).integer :=
    (x'.comp (algebraMap A A')).codRestrict _ fun a => (hi _).2 (hx a)
  exact (hi _).1 ((Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral
    (IsIntegral.map_of_comp_eq y x' rfl (Algebra.IsIntegral.isIntegral (R := A) b)))

theorem of_covectors {A : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CharZero A] (x₀ : Sp A ⟶ X) {g : ℕ}
    {e : Fin g → (Sp (DualNumber A) ⟶ t.G.left)} (he : IsTanBasis t x₀ e) (q k : ℕ) (A' : Type) [CommRing A']
    [IsDomain A'] [Algebra A A'] [Module.Finite A A'] (hinj : Function.Injective (algebraMap A A'))
    (J : Type) [Fintype J] (h : J → Fin g → A') (c : ℕ) (hc : c ≠ 0) (hh : ∀ i, ∃ j, h j = Pi.single i (c : A'))
    (hΛ : ∀ (p : ℕ) [Fact p.Prime] (y : A' →+* ↥(intO ℂ_[p])) (b : Fin g → ℂ_[p])
      (w : Sp (DualNumber ℂ_[p]) ⟶ t.G.left),
      IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ spMap y ≫ spMap (algebraMap A A') ≫ x₀)
        (fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ spMap (dualMap y) ≫ spMap (dualMap (algebraMap A A')) ≫ e i)
        b w →
      (w ∈ lat t p (spMap (intO ℂ_[p]).subtype ≫ spMap y ≫ spMap (algebraMap A A') ≫ x₀) (decide (p = q)) ↔
        ∀ j, ‖∑ i, (y (h j i) : ℂ_[p]) * b i‖ ≤ 1)) :
    ∃ (d : ℕ+) (n : ℕ) (B : Fin n → MvPolynomial (Fin k → Fin g) A), (∀ i, (B i).IsHomogeneous d) ∧ (∀ s, ∃ (i : Fin n) (c : ℕ), c ≠ 0 ∧ B i = MvPolynomial.C (c : A) * (MvPolynomial.X s : MvPolynomial (Fin k → Fin g) A) ^ (d : ℕ)) ∧ ∀ (p : ℕ) [Fact p.Prime] (x : A →+* ℂ_[p]), (∀ a, ‖x a‖ ≤ 1) → ∀ (m : ℕ) (hk : k ≤ m) (u : Fin m → (Sp (DualNumber ℂ_[p]) ⟶ t.G.left)) (a : Fin m → Fin g → ℂ_[p]), LinearIndependent ℂ_[p] a → (∀ l, IsCombAtG t (spMap x ≫ x₀) (fun i => spMap (dualMap x) ≫ e i) (a l) (u l)) → ((d : ℕ) : ℝ) * ∑ l : Fin k, Real.log (GlobalTheory.ShFam.Pad.grNorm t (spMap x ≫ x₀) (lat t p (spMap x ≫ x₀) (decide (p = q))) u (Fin.castLE hk l)) = Real.log (⨆ i, ‖MvPolynomial.eval₂ x (minor a hk) (B i)‖) := by
  obtain ⟨d, n, B, h1, h2, h3⟩ := exists_poly A A' hinj g k J h c hc hh
  refine ⟨d, n, B, h1, h2, fun p _ x hx m hk u a ha hu => h3 ℂ_[p] x m hk a ha _ fun x' hx' l => ?_⟩
  subst hx'
  let y : A' →+* ↥(intO ℂ_[p]) := x'.codRestrict _ fun b => norm_le_one x' hx b
  have e1 : x' = (intO ℂ_[p]).subtype.comp y := rfl
  refine grNorm_eq t (isTanBasis_map t _ he).1 (P := fun b => ∀ j, ‖∑ i, x' (h j i) * b i‖ ≤ 1) ?_ hu l
  have := hΛ p y
  rw [e1]
  simpa only [spMap_comp, spMap_dual_comp, Category.assoc, RingHom.comp_apply, Subring.coe_subtype] using this

theorem norm_sum_single {g : ℕ} {A' : Type} [CommRing A'] (y : A' →+* ↥(intO C)) (c : ℕ) (b : Fin g → C) (i : Fin g) :
    ∑ i', (y ((Pi.single i (c : A') : Fin g → A') i') : C) * b i' = c * b i := by
  rw [Finset.sum_eq_single i (fun i' _ hi => by simp [Pi.single_eq_of_ne hi]) (by simp)]
  simp

theorem wedge_norm_max : HTBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X), X.IsSeparated → ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [CharZero A] (x₀ : Sp A ⟶ X) (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ t.G.left)), IsTanBasis t x₀ e → ∀ q k : ℕ, ∃ (d : ℕ+) (n : ℕ) (B : Fin n → MvPolynomial (Fin k → Fin g) A), (∀ i, (B i).IsHomogeneous d) ∧ (∀ s, ∃ (i : Fin n) (c : ℕ), c ≠ 0 ∧ B i = MvPolynomial.C (c : A) * (MvPolynomial.X s : MvPolynomial (Fin k → Fin g) A) ^ (d : ℕ)) ∧ ∀ (p : ℕ) [Fact p.Prime] (x : A →+* ℂ_[p]), (∀ a, ‖x a‖ ≤ 1) → ∀ (m : ℕ) (hk : k ≤ m) (u : Fin m → (Sp (DualNumber ℂ_[p]) ⟶ t.G.left)) (a : Fin m → Fin g → ℂ_[p]), LinearIndependent ℂ_[p] a → (∀ l, IsCombAtG t (spMap x ≫ x₀) (fun i => spMap (dualMap x) ≫ e i) (a l) (u l)) → ((d : ℕ) : ℝ) * ∑ l : Fin k, Real.log (GlobalTheory.ShFam.Pad.grNorm t (spMap x ≫ x₀) (lat t p (spMap x ≫ x₀) (decide (p = q))) u (Fin.castLE hk l)) = Real.log (⨆ i, ‖MvPolynomial.eval₂ x (minor a hk) (B i)‖) := by
  intro hHT E _ _ _ H X _ t hX A _ _ _ _ _ x₀ g e he q k
  by_cases hq : q.Prime
  · obtain ⟨A', _, _, _, _, hinj, _, hζ, hsp⟩ := GlobalTheory.T.exists_finite_extension_splitting_torsion E H X t A x₀ q hq.ne_zero
    have : CharZero A' := charZero_of_injective_algebraMap hinj
    have he' := isTanBasis_map t (algebraMap A A') he
    obtain ⟨n, h, hh⟩ := GlobalTheory.T.exists_tangent_presentation_prime E H X t A' _ g _ he' q hq hζ hsp
    refine of_covectors t x₀ he q k A' hinj (Fin n ⊕ Fin g) (Sum.elim h fun i => Pi.single i (q : A')) q hq.ne_zero
      (fun i => ⟨Sum.inr i, rfl⟩) fun p _ y b w hw => ?_
    simp only [Sum.forall, Sum.elim_inl, Sum.elim_inr, norm_sum_single]
    have hn : ∀ r : ℕ, ‖(r : ℂ_[p])‖ = ‖(r : ℚ_[p])‖ := fun r => by
      rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap']
    by_cases hp : p = q
    · subst hp
      rw [decide_eq_true rfl]
      exact GlobalTheory.T.unique_integral_lift_norm_p_inverse hHT E H X t p ℂ_[p] (by rw [hn, Padic.norm_p]) _ (ext_intO hX _) g _
        (isTanBasis_map t y he') n (fun j i => y (h j i)) (hh ℂ_[p] y).1 (hh ℂ_[p] y).2 b w hw
    · rw [decide_eq_false hp]
      have h1 : ‖(q : ℂ_[p])‖ = 1 := by
        rw [hn, Padic.norm_natCast_eq_one_iff]
        exact (Nat.coprime_primes Fact.out hq).2 hp
      refine (mem_latDR t hX (isTanBasis_map t y he') b w hw).trans ?_
      simp only [norm_mul, h1, _root_.one_mul]
      refine ⟨fun hb => ⟨fun j => ?_, hb⟩, fun hb => hb.2⟩
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
      rw [norm_mul]
      exact mul_le_one₀ (y (h j i)).2 (norm_nonneg _) (hb i)
  · have he' := isTanBasis_map t (algebraMap A A) he
    refine of_covectors t x₀ he q k A (fun _ _ h => h) (Fin g) (fun i => Pi.single i ((1 : ℕ) : A)) 1 one_ne_zero
      (fun i => ⟨i, rfl⟩) fun p hp y b w hw => ?_
    simp only [norm_sum_single]
    rw [decide_eq_false fun h : p = q => hq (h ▸ hp.out)]
    simp only [Nat.cast_one, _root_.one_mul]
    exact mem_latDR t hX (isTanBasis_map t y he') b w hw

end GlobalTheory.LineNorm.WedgeMax
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsResidueNeZeroOneStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_residue_ne_zero_one : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t _ _ c =>
  ∀ PP ∈ t.r.z.R.Pg, ∃ x : Formalism.L2.DIV.kP PP, x ≠ 0 ∧ x ≠ 1 := by
  first | exact @GlobalTheory.ResThree.main | exact GlobalTheory.ResThree.main | (intros; apply GlobalTheory.ResThree.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentReadingBundleStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponent_reading_bundle : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP) (hE : GlobalTheory.PlugPt.HasExp N) (K : Ctx) (q : WPt (prmR N S Γ).s K) (c : ℝ) (b : Bundle (q.w.D q.Z) q.O c) (_ : BWit (p := prmR N S Γ) q b) (t : b.Comparison₂), GlobalTheory.PlugPt.pinPt (GlobalTheory.PlugPt.NRead.of RX hE (SXE S) (OX Γ)) K q c (b.part t).pt := by
  first | exact @GlobalTheory.PlugPt.pinPt_part_of_wit | exact GlobalTheory.PlugPt.pinPt_part_of_wit | (intros; apply GlobalTheory.PlugPt.pinPt_part_of_wit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FamilyMetricsSmooth
section
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory

theorem metsOf_smooth : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (Φ : s.Flag) (k : s.Comp) (σ : D.what₂.LL →+* ℂ) (n : Pad.Letter S.Dw → ℤ), (∀ R : ℝ, 2 ≤ R → (cxSt D.what₂.LL).mSmooth _ σ _ (metsOf x Φ k (some R) σ n)) ∧ (cxSt D.what₂.LL).mSmooth _ σ _ (refMet x Φ k σ n) ∧ Var.Met.SmoothOn (metsOf x Φ k none σ n) {p | (Φ.C k).π (Var.base p) ∉ genBd s.T.Z} := by
  intro D A N j S κ s x Φ k σ n
  exact ⟨fun R hR => (GlobalTheory.T.eigen_metric_flag_compactification _ _ _ _ _ _ _ _ _ _ _ (Φ.C k) σ _ _ isOpen_univ
      (GlobalTheory.T.eigen_metric_smooth_of_hodge D A N j S κ s x _ R hR (GlobalTheory.T.hodge_metric_smooth_off_boundary D A N j S κ s x _)) n).2,
    (GlobalTheory.T.eigen_metric_flag_compactification _ _ _ _ _ _ _ _ _ _ _ (Φ.C k) σ _ _ isOpen_univ (x.smoothOn_eigMet _) n).2,
    (GlobalTheory.T.eigen_metric_flag_compactification _ _ _ _ _ _ _ _ _ _ _ (Φ.C k) σ _ _ (isOpen_not_liesIn _) (GlobalTheory.T.hodge_metric_smooth_off_boundary D A N j S κ s x _) n).2⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteHomEqOfFramesKeepMatricesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteHom_eq_of_frames_keep_matrices : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P P' : principalLevelFrame.RowPsi V n), GlobalTheory.MtRead.IdFrame hF P → GlobalTheory.MtRead.IdFrame hF P' → ∀ g, (finHom V).rangeRestrict (P.ψ g) = (finHom V).rangeRestrict (P'.ψ g) := by
  first | exact @GlobalTheory.FrameFinPart.finHom_eq_of_idFrame | exact GlobalTheory.FrameFinPart.finHom_eq_of_idFrame | (intros; apply GlobalTheory.FrameFinPart.finHom_eq_of_idFrame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentCarriesEveryFrameFlagStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagSpaceComponent_carries_every_frame_flag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (N : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ N) (Φ : FlagTor Z e U), ∀ (i : U.Comp) (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ gen Z), x ≫ genStr Z = spMap χ → ∀ (g g' : EigFrame Z χ (x ≫ genι Z)) (p : Sp K ⟶ (Φ.C i).Y.X), p ≫ (Φ.C i).π = x → (Φ.C i).Carries p g → ∃ p' : Sp K ⟶ (Φ.C i).Y.X, p' ≫ (Φ.C i).π = x ∧ (Φ.C i).Carries p' g' := by
  first | exact @GlobalTheory.FlagFibre.carries_every | exact GlobalTheory.FlagFibre.carries_every | (intros; apply GlobalTheory.FlagFibre.carries_every <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentClassifyingMapBijectiveGeomPoiStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagSpaceComponent_classifyingMap_bijective_geomPoints : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j → j ≫ genStr Z ≫ spMap e.toRingHom = X.str → ∀ (f : C.Y.X ⟶ X.X), f ≫ j = C.π → ∀ (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn), Tied e X j f₀ Eb A₀ → (∀ (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ X.X), x ≫ j ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ j ≫ genι Z), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x ∧ C.Carries p g) → ∀ (Y' : Var F) (φ' : X.Fn →ₐ[F] Y'.Fn) (f' : Y'.X ⟶ X.X) (S' : Fr (ratOf Y') Dw.mult Dw.mult), Refines Eb S' φ' f' → ∃ h : C.Y.X ⟶ Y'.X, h ≫ f' = f ∧ ∀ (K : Type) [Field K] [IsAlgClosed K], Function.Bijective (fun p : Sp K ⟶ C.Y.X => p ≫ h) := by
  first | exact @GlobalTheory.ShFam.ClsMap.main | exact GlobalTheory.ShFam.ClsMap.main | (intros; apply GlobalTheory.ShFam.ClsMap.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.G0LiftUnitaryCentralFrameStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.g0_lift_unitary_central_frame : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t _ _ _ =>
  ∀ s, ∃ L : G0g (w.st Z).toD7.nd → Formalism.AUTREP.GAf (w.st Z).toD7.host.E (w.st Z).toD7.R.nV,
    GlobalTheory.PendOf.IsTypeGroupBlockLift (w.st Z).toD7 (w.st Z).toD7.R.nV L ∧ (∀ g, L g ∈ ReciprocityTheory.Aut.Umax (w.st Z).toD7.host.E (w.st Z).toD7.R.nV) ∧
    ∀ g (s' : ReciprocityTheory.Aut.SplitPlace (w.st Z).toD7.host.E) (φ : GlobalTheory.CenFrame.Os s' →+* Formalism.L2.DIV.kP s'.w), GlobalTheory.CenFrame.IsResidue s' φ →
      (s'.w ∈ t.r.z.R.Q s → ∃ y, GlobalTheory.CenFrame.IsCompOf s' (L g) y ∧ Matrix.GeneralLinearGroup.map φ y = 1) ∧
      ∀ hP : s'.w ∈ t.r.z.R.Pg, ∃ y, GlobalTheory.CenFrame.IsCompOf s' (L g) y ∧
        GlobalTheory.FrameBlockDiagonal.IsBlockDiagonalWithIdentity (t.r.z.R.eG ((t.r.z.R.eG.trans t.r.z.cG).symm g) ⟨s'.w, hP⟩) (Matrix.GeneralLinearGroup.map φ y) := by
  first | exact @GlobalTheory.BlockLiftFrame.atMem | exact GlobalTheory.BlockLiftFrame.atMem | (intros; apply GlobalTheory.BlockLiftFrame.atMem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricHalfToAnalyticDataEnlargedBase
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 4000000 in
theorem _root_.GlobalTheory.T.geometricHalf_to_analyticData_enlargedBase : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
    ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
      (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
      (∀ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y ∈ B'.LL0) →
      (∀ x ∈ B'.Ks, ∃ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y = x) →
      (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
      Formalism.L2.Pj.LawsCore core'.toCore → core'.Q.Canon → (∀ j, 1 ≤ (core'.Q.Dw j).p + (core'.Q.Dw j).q) → core'.pb = f'.P.pb →
      letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr : TrI B' w'.px)
        (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr) core'.Q.c.F)
        (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr) cG' ∧
        LevOf (w'.st Z') w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) R'.toLevCh ∧ IsPlacewiseIdentity (w'.st Z') (px := w'.px) R'.eG ∧
        GoodSet (w'.st Z') (px := w'.px) (R'.eG.trans cG') Xg ∧ MuOf (w'.st Z') w'.I T' {v | B'.places.resChar v ∈ T'.pl} R'.mu R'.twPl ∧
        BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr R'.toRealDat ∧ R'.toRealDat.ExAt ∧ RSide z {v | B'.places.resChar v ∈ T'.pl} R' → (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ x' ∈ (R'.FW i').WK, ∃ x ∈ (z.R.FW i).WK,
          ∀ ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ y, (w'.st Z').toD7.what₂.embLL (ι y) = (w.st Z).toD7.what₂.embLL y) → CrdOver ι x x') →
        ∃ geo : GlobalTheory.RealGeo.GeoHalf core' R'.toRealDat (fun _ => 1), GlobalTheory.RealGeo.InGeo geo ∧
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
          HEq (geo.v₀ i' (w'.st Z').toD7.what₂.embLL) (z.geo.v₀ i (w.st Z).toD7.what₂.embLL) ∧
          (∀ φ φ', HEq φ' φ → HEq ((R'.FW i').j (w'.st Z').toD7.what₂.embLL (geo.fw.e i' φ' : (R'.FW i').WK).1)
            ((z.R.FW i).j (w.st Z).toD7.what₂.embLL (z.geo.fw.e i φ : (z.R.FW i).WK).1)) ∧
          (HEq (geo.κ i').aP (z.geo.κ i).aP ∧ HEq (geo.κ i').aM (z.geo.κ i).aM ∧ (geo.κ i').n = (z.geo.κ i).n)) ∧
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ φ φ', HEq φ' φ →
          ∀ (k : Fin (z.R.nW i)) (k' : Fin (R'.nW i')), (k : ℕ) = k' →
          (w'.st Z').toD7.what₂.embLL ((geo.fw.e i' φ' : (R'.FW i').WK).1 k') = (w.st Z).toD7.what₂.embLL ((z.geo.fw.e i φ : (z.R.FW i).WK).1 k))) := by
  intro _ _ h3 _ _ _ _
  refine (GlobalTheory.Mem.R3.Rw.inGeo_stepW h3 Pinned).trans (Step.of_all fun K B' f' T' _ _ _ _ w' H => ?_)
  intro B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV core' alg' ha1 ha2 ha3 hc hL hC hD hpb Xg tr R' cG' s1 _
  letI := alg'
  obtain ⟨hPins, hLev, -, -, -, hBrg, hEx', hRS⟩ := s1
  have hex : ∃ ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL,
      ∀ x, (w'.st Z').toD7.what₂.embLL (ι x) = (w.st Z).toD7.what₂.embLL x := ⟨(by with_unfolding_all exact ((enlEmb hE.2.2.2) :)), (by with_unfolding_all exact ((enlEmb_spec hE.2.2.2) :))⟩
  refine hex.elim fun ι hι => ?_
  have hcomp : (w'.st Z').toD7.what₂.embLL.comp ι = (w.st Z).toD7.what₂.embLL := RingHom.ext hι
  have hfw := UpperTheory.Mem.GeoExt.exists_fw B B' f f' T T' w w' hE.1 Z hX Wt z Z' hX' {v | B'.places.resChar v ∈ T'.pl} core' alg' ha1 hc hL
    Xg tr R' hRS.1 hf hLev ι hι
  refine hfw.elim fun κ' hfw => hfw.elim fun v₀' hfw => hfw.elim fun fw' hfw => ?_
  have hκ := hfw.1
  have hv := hfw.2.1
  have he := hfw.2.2
  have hcrd : ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ φ φ', HEq φ' φ →
      ∀ (k : Fin (z.R.nW i)) (k' : Fin (R'.nW i')), (k : ℕ) = k' →
      (w'.st Z').toD7.what₂.embLL ((fw'.e i' φ' : (R'.FW i').WK).1 k') =
        (w.st Z).toD7.what₂.embLL ((z.geo.fw.e i φ : (z.R.FW i).WK).1 k) :=
    fun i i' hi φ φ' hφ k k' hk => (congrArg _ ((he i i' hi φ φ' hφ).2 k k' hk)).trans (hι _)
  have hv0 : ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
      HEq (v₀' i' (w'.st Z').toD7.what₂.embLL) (z.geo.v₀ i (w.st Z).toD7.what₂.embLL) :=
    fun i i' hi => (hv i i' hi _).trans (congr_arg_heq (z.geo.v₀ i) hcomp)
  have hMW : GeoTies.MWOver z.R.toRealDat R'.toRealDat := fun i i' hi ι' hι' σ' => by
    have hcl := (((hRS.1.2.2.2.2.2.2.2.2.2.2.2.2.1 i i' hi).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ι' hι').1 σ').1
    exact ⟨hcl.1, hcl.2.1, hcl.2.2.1, hcl.2.2.2.1, hcl.2.2.2.2.1, hcl.2.2.2.2.2.1, hcl.2.2.2.2.2.2.1⟩
  have hO := UpperTheory.Mem.GeoExt.exists_omOver z hE hf hpx hF.2.2.2 core' hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1
    hc.2.2.2.2.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.2.2.2.2 R' cG' hPins hLev hBrg hRS κ' v₀'
    (GlobalTheory.OneMapRefObj.tieIn_of_fwTie fw')
  refine hO.elim fun O' hO => ?_
  have hOP := hO.1
  have hOm := hO.2
  have t := UpperTheory.Mem.GeoExt.ties_enl w w' Z Z' hX hX' Wt {v | B'.places.resChar v ∈ T'.pl} z hE hpx core' alg' ha1 hc Xg tr R' cG' hPins hRS
    κ' hκ v₀' fw' hcrd hv0 O' hOP hOm hF.1 hH.unif hEx' hMW
  refine ⟨⟨κ', v₀', fw', t.1, O', hOP, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2⟩, H Z' hX' _ core' alg' Xg tr R' cG' hPins hEx' _ _,
    fun i i' hi => ⟨hv0 i i' hi, fun φ φ' hφ => ?_, hκ i i' hi⟩, hcrd⟩
  have hj := (((hRS.1.2.2.2.2.2.2.2.2.2.2.2.2.1 i i' hi).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ι hι).1
    (w'.st Z').toD7.what₂.embLL).2.2.2 _ _ (he i i' hi φ φ' hφ)
  exact hj.trans (congr_arg_heq (fun σ => (z.R.FW i).j σ (z.geo.fw.e i φ : (z.R.FW i).WK).1) hcomp)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodFiberTypesAllStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_fiber_types_all : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ _ _ _ _ _ x => LA hL x → GoodFTAll (Dof x) := by
  first | exact @GlobalTheory.GoodFirst.goodFTAll_allSt | exact GlobalTheory.GoodFirst.goodFTAll_allSt | (intros; apply GlobalTheory.GoodFirst.goodFTAll_allSt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrassmannProductIntegralEqFlagDegreeWeightStatement
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grassmannProductIntegral_eq_flagDegree_weight : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (la : GlobalTheory.AllWt.Weight Dw) (R : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) (D : ℕ), D = Fintype.card (GlobalTheory.AllWt.Psi H) * ((Dw.p + Dw.q) * (Dw.p + Dw.q - 1) / 2) → antisymm ((∑ x : Root Dw.mult, MvPolynomial.C (-(GlobalTheory.AllWt.exOf Dw la 0 (some x) : ℝ)) * MvPolynomial.X x) ^ D) = chernRoots Dw.mult R * rootDiscr Dw.mult → intGr H Dw R = Formalism.DegreeFormula.flagDeg (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) (fun τ i => (la τ i : ℝ)) := by
  first | exact @GlobalTheory.GrassTop.intGr_eq_flagDeg | exact GlobalTheory.GrassTop.intGr_eq_flagDeg | (intros; apply GlobalTheory.GrassTop.intGr_eq_flagDeg <;> assumption)
end


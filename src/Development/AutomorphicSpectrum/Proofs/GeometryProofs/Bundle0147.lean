import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPeriodAtRestrict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0009
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0023
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0022
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0138
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AddJFintype
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerI5OfReference
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartOfSmoothCoords
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncRes

theorem exists_cover_basicOpen {Z : Scheme.{0}} {W : Z.Opens} (hW : IsAffineOpen W) {n : ℕ}
    (V : Fin n → Z.affineOpens) (hV : ∀ y : Z, ∃ j, y ∈ (V j : Z.Opens)) :
    ∃ (m : ℕ) (u c : Fin m → Γ(Z, W)), ∑ l, c l * u l = 1 ∧
      ∀ l, ∃ (j : Fin n) (v : Γ(Z, (V j : Z.Opens))), Z.basicOpen (u l) = Z.basicOpen v := by
  classical
  let s : Set Γ(Z, W) :=
    {f | ∃ (j : Fin n) (v : Γ(Z, (V j : Z.Opens))), Z.basicOpen f = Z.basicOpen v}
  have hs : Ideal.span s = ⊤ := by
    rw [← hW.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨j, hj⟩ := hV x
    obtain ⟨f, g, e, hxf⟩ := exists_basicOpen_le_affine_inter hW (V j).2 x ⟨hx, hj⟩
    exact Opens.mem_iSup.2 ⟨⟨f, j, g, e⟩, hxf⟩
  have h1 : (1 : Γ(Z, W)) ∈ Ideal.span s := hs ▸ Submodule.mem_top
  obtain ⟨c, hc, hsum⟩ := Submodule.mem_span_set.1 h1
  let e := c.support.equivFin.symm
  refine ⟨c.support.card, fun l => (e l : Γ(Z, W)), fun l => c (e l), ?_, fun l => hc (e l).2⟩
  rw [← hsum, Finsupp.sum, ← Finset.sum_coe_sort c.support]
  exact Equiv.sum_comp e fun x : c.support => c x * (x : Γ(Z, W))

theorem smooth_secAlgebra {Z : Scheme.{0}} (g : Z ⟶ Sp ℚ) (e : ℕ)
    (hsm : SmoothOfRelativeDimension e g) {D : Z.Opens} (hD : IsAffineOpen D) :
    @Algebra.Smooth ℚ _ Γ(Z, D) _ (secAlgebra g D) := by
  have h0 : Smooth g := hsm.smooth
  have h1 := Smooth.smooth_appLE (f := g) (isAffineOpen_top _) hD (fun _ _ => trivial)
  exact RingHom.Smooth.propertyIsLocal.respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of ℚ)).symm.commRingCatIsoToRingEquiv h1

theorem coords_of_formallyEtale {R S : Type} [CommRing R] [CommRing S] [Algebra ℚ R] [Algebra ℚ S]
    [Algebra R S] [IsScalarTower ℚ R S] [Algebra.FormallyEtale R S] {e : ℕ} (z : Fin e → R)
    (h1 : LinearIndependent R fun i => KaehlerDifferential.D ℚ R (z i))
    (h2 : Submodule.span R (Set.range fun i => KaehlerDifferential.D ℚ R (z i)) = ⊤) :
    LinearIndependent S (fun i => KaehlerDifferential.D ℚ S (algebraMap R S (z i))) ∧
      Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (algebraMap R S (z i))) = ⊤ := by
  let b := Module.Basis.mk h1 h2.ge
  let b' := (b.baseChange S).map (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale ℚ R S)
  have hb : (fun i => KaehlerDifferential.D ℚ S (algebraMap R S (z i))) = b' := by
    funext i
    simp [b', b, KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply]
  rw [hb]
  exact ⟨b'.linearIndependent, b'.span_eq⟩

theorem exists_point_of_prime {Z : Scheme.{0}} {D : Z.Opens} (hD : IsAffineOpen D)
    (q : Ideal Γ(Z, D)) (hq : q.IsPrime) :
    ∃ t ∈ D, ∀ s : Γ(Z, D), s ∈ q ↔ t ∉ Z.basicOpen s := by
  refine ⟨hD.fromSpec ⟨q, hq⟩, hD.fromSpec_preimage_self.ge trivial, fun s => ?_⟩
  have h := hD.fromSpec_preimage_basicOpen s
  have h2 : (hD.fromSpec ⟨q, hq⟩ ∈ Z.basicOpen s) ↔ (⟨q, hq⟩ : PrimeSpectrum Γ(Z, D)) ∈ PrimeSpectrum.basicOpen s := by
    rw [← h]
    rfl
  rw [h2]
  simp

theorem range_valMap_basicOpen {Ω : Type} [Field Ω] [CharZero Ω] {Z : Scheme.{0}} (ζ : Sp Ω ⟶ Z)
    {W : Z.Opens} (hW : IsAffineOpen W) (h : ⊤ ≤ ζ ⁻¹ᵁ W) (A : Subalgebra ℚ Ω)
    (hA : Set.range (valMap ζ W h).hom = A) (u : Γ(Z, W)) (hu : valR ζ W u ≠ 0) (D : Z.Opens)
    (hDu : D = Z.basicOpen u) :
    ∃ hD : ⊤ ≤ ζ ⁻¹ᵁ D, Set.range (valMap ζ D hD).hom =
      (Algebra.adjoin ℚ (insert (valR ζ W u)⁻¹ (A : Set Ω)) : Subalgebra ℚ Ω) := by
  subst hDu
  have hD : ⊤ ≤ ζ ⁻¹ᵁ Z.basicOpen u := (le_preimage_basicOpen_iff ζ h u).2 (isUnit_iff_ne_zero.2 hu)
  have hle : Z.basicOpen u ≤ W := Z.basicOpen_le u
  have hres : ∀ w : Γ(Z, W), (valMap ζ _ hD).hom ((Z.presheaf.map (homOfLE hle).op).hom w) = valR ζ W w :=
    fun w => by rw [← valR_eq _ _ hD, valR_res ζ hle hD]
  refine ⟨hD, Set.Subset.antisymm ?_ ?_⟩
  · rintro _ ⟨x, rfl⟩
    have := hW.isLocalization_basicOpen u
    obtain ⟨k, a, ha⟩ := IsLocalization.Away.surj u x
    have h1 := congrArg (valMap ζ _ hD).hom ha
    rw [map_mul, map_pow] at h1
    have h2 : ∀ t : Γ(Z, W), (valMap ζ _ hD).hom (algebraMap Γ(Z, W) Γ(Z, Z.basicOpen u) t) = valR ζ W t :=
      hres
    rw [h2, h2] at h1
    have h3 : (valMap ζ _ hD).hom x = valR ζ W a * ((valR ζ W u)⁻¹) ^ k := by
      rw [← h1, inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hu), mul_one]
    have hv : ∀ w : Γ(Z, W), valR ζ W w ∈ (A : Set Ω) := fun w => by
      rw [← hA, valR_eq _ _ h]; exact ⟨w, rfl⟩
    rw [h3]
    exact Subalgebra.mul_mem _ (Algebra.subset_adjoin (Set.mem_insert_of_mem _ (hv a)))
      (Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_insert _ _)) _)
  · intro x hx
    have hAr : ∀ a ∈ A, a ∈ Set.range (valMap ζ _ hD).hom := fun a ha => by
      have : a ∈ Set.range (valMap ζ W h).hom := by rw [hA]; exact ha
      obtain ⟨w, rfl⟩ := this
      exact ⟨_, (hres w).trans (valR_eq _ _ h _)⟩
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · have hunit : IsUnit ((Z.presheaf.map (homOfLE hle).op).hom u) :=
          RingedSpace.isUnit_res_basicOpen Z.toLocallyRingedSpace.toRingedSpace u
        obtain ⟨b, hb⟩ := hunit.exists_right_inv
        refine ⟨b, (inv_eq_of_mul_eq_one_right ?_).symm⟩
        rw [← hres u, ← map_mul, hb, map_one]
      · exact hAr x hx
    | algebraMap r => exact hAr _ (Subalgebra.algebraMap_mem _ r)
    | add x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, map_add _ _ _⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a * b, map_mul _ _ _⟩

theorem snc_on_basicOpen {Ω : Type} [Field Ω] [CharZero Ω] {Z : Scheme.{0}} (ζ : Sp Ω ⟶ Z)
    [IsDominant ζ] [IsReduced Z] (g : Z ⟶ Sp ℚ) (e : ℕ) (T : Set Z)
    (hsm : SmoothOfRelativeDimension e g) {W : Z.Opens} (hW : IsAffineOpen W) (h : ⊤ ≤ ζ ⁻¹ᵁ W)
    (A : Subalgebra ℚ Ω) (hA : Set.range (valMap ζ W h).hom = A) (σ : Γ(Z, W))
    (hσ : ∀ t ∈ W, t ∈ T ↔ t ∉ Z.basicOpen σ) (u : Γ(Z, W)) (hu : valR ζ W u ≠ 0)
    {V : Z.Opens} (hV : IsAffineOpen V) (v : Γ(Z, V)) (huv : Z.basicOpen u = Z.basicOpen v)
    (z : Fin e → Γ(Z, V)) (k : ℕ) (hk : k ≤ e) (hz : IsCoords g V z)
    (hT : (V : Set Z) ∩ T = {y | y ∈ V ∧ ∃ i : Fin e, (i : ℕ) < k ∧ y ∉ Z.basicOpen (z i)})
    (S : Subalgebra ℚ Ω) (hS : S = Algebra.adjoin ℚ (insert (valR ζ W u)⁻¹ (A : Set Ω))) :
    Algebra.Smooth ℚ S ∧ ∃ (z : Fin e → S) (n : ℕ), n ≤ e ∧
      LinearIndependent S (fun i => KaehlerDifferential.D ℚ S (z i)) ∧
      Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤ ∧
      ∀ q : Ideal S, q.IsPrime →
        ((∀ s : S, (s : Ω) = valR ζ W σ → s ∈ q) ↔ ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q) := by
  obtain ⟨hD, hr⟩ := range_valMap_basicOpen ζ hW h A hA u hu (Z.basicOpen v) huv.symm
  rw [← hS] at hr
  have hDaff : IsAffineOpen (Z.basicOpen v) := hV.basicOpen v
  have hDW : Z.basicOpen v ≤ W := huv ▸ Z.basicOpen_le u
  have hDV : Z.basicOpen v ≤ V := Z.basicOpen_le v
  letI iV := secAlgebra g V
  letI iD := secAlgebra g (Z.basicOpen v)
  let ψ := (valMap ζ (Z.basicOpen v) hD).hom
  have hψ : ∀ x, ψ x ∈ S := fun x => by
    have : ψ x ∈ Set.range ψ := ⟨x, rfl⟩
    rw [show Set.range ψ = (S : Set Ω) from hr] at this
    exact this
  let φ : Γ(Z, Z.basicOpen v) ≃+* S := RingEquiv.ofBijective (ψ.codRestrict S hψ) (by
    refine ⟨fun a b hab => valMap_injective ζ hD (congrArg Subtype.val hab), fun s => ?_⟩
    have hs : (s : Ω) ∈ Set.range ψ := by
      rw [show Set.range ψ = (S : Set Ω) from hr]
      exact s.2
    obtain ⟨x, hx⟩ := hs
    exact ⟨x, Subtype.ext hx⟩)
  have hφ : ∀ x, (φ x : Ω) = ψ x := fun _ => rfl
  haveI hs0 : Algebra.Smooth ℚ Γ(Z, Z.basicOpen v) := smooth_secAlgebra g e hsm hDaff
  have hsmooth : Algebra.Smooth ℚ S := Algebra.Smooth.of_equiv φ.toRatAlgEquiv
  refine ⟨hsmooth, ?_⟩

  haveI := hV.isLocalization_basicOpen v
  haveI : Algebra.FormallyEtale Γ(Z, V) Γ(Z, Z.basicOpen v) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers v)
  haveI : IsScalarTower ℚ Γ(Z, V) Γ(Z, Z.basicOpen v) :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  obtain ⟨c1, c2⟩ := coords_of_formallyEtale (R := Γ(Z, V)) (S := Γ(Z, Z.basicOpen v)) z hz.1 hz.2

  letI iS : Algebra Γ(Z, Z.basicOpen v) S := φ.toRingHom.toAlgebra
  haveI : Algebra.FormallyEtale Γ(Z, Z.basicOpen v) S :=
    Algebra.FormallyEtale.of_equiv (AlgEquiv.ofRingEquiv (f := φ) fun _ => rfl)
  haveI : IsScalarTower ℚ Γ(Z, Z.basicOpen v) S :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  obtain ⟨d1, d2⟩ := coords_of_formallyEtale (R := Γ(Z, Z.basicOpen v)) (S := S) _ c1 c2
  refine ⟨_, k, hk, d1, d2, fun q hq => ?_⟩
  have hq' : (q.comap φ.toRingHom).IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨t, htD, ht⟩ := exists_point_of_prime hDaff _ hq'
  have hmem : ∀ x, φ x ∈ q ↔ t ∉ Z.basicOpen x := ht
  have htV : t ∈ V := hDV htD
  have htW : t ∈ W := hDW htD
  have hzt : ∀ i, algebraMap Γ(Z, Z.basicOpen v) S (algebraMap Γ(Z, V) Γ(Z, Z.basicOpen v) (z i)) ∈ q ↔
      t ∉ Z.basicOpen (z i) := fun i => by
    refine (hmem _).trans (not_congr ?_)
    have := Z.basicOpen_res (z i) (homOfLE hDV).op
    rw [show algebraMap Γ(Z, V) Γ(Z, Z.basicOpen v) (z i) =
      (Z.presheaf.map (homOfLE hDV).op).hom (z i) from rfl, this]
    exact ⟨fun h => h.2, fun h => ⟨htD, h⟩⟩
  let sσ : Γ(Z, Z.basicOpen v) := (Z.presheaf.map (homOfLE hDW).op).hom σ
  have hsσ : (φ sσ : Ω) = valR ζ W σ := by
    rw [hφ, ← valR_res ζ hDW hD σ, valR_eq _ _ hD]
  have hσt : φ sσ ∈ q ↔ t ∈ T := by
    refine (hmem _).trans ?_
    rw [hσ t htW, not_iff_not, Z.basicOpen_res σ (homOfLE hDW).op]
    exact ⟨fun h => h.2, fun h => ⟨htD, h⟩⟩
  have hTt : t ∈ T ↔ ∃ i : Fin e, (i : ℕ) < k ∧ t ∉ Z.basicOpen (z i) := by
    have h1 : t ∈ (V : Set Z) ∩ T ↔ t ∈ T := ⟨fun h => h.2, fun h => ⟨htV, h⟩⟩
    rw [← h1, hT]
    exact ⟨fun h => h.2, fun h => ⟨htV, h⟩⟩
  constructor
  · intro H
    obtain ⟨i, hi, hit⟩ := hTt.1 (hσt.1 (H _ hsσ))
    exact ⟨i, hi, (hzt i).2 hit⟩
  · rintro ⟨i, hi, hit⟩ s hs
    have : s = φ sσ := Subtype.ext (hs.trans hsσ.symm)
    rw [this]
    exact hσt.2 (hTt.2 ⟨i, hi, (hzt i).1 hit⟩)

theorem sncChart_of_coords (Ω : Type) [Field Ω] [CharZero Ω] (Z : Scheme.{0}) (ζ : Sp Ω ⟶ Z)
    [IsDominant ζ] [IsReduced Z] (g : Z ⟶ Sp ℚ) (e : ℕ) (T : Set Z)
    (hsm : SmoothOfRelativeDimension e g) (hc : HasSncCoords g e T) (W : Z.Opens)
    (hW : IsAffineOpen W) (h : ⊤ ≤ ζ ⁻¹ᵁ W) (A : Subalgebra ℚ Ω)
    (hA : Set.range (valMap ζ W h).hom = A) (σ : Γ(Z, W))
    (hσ : ∀ t ∈ W, t ∈ T ↔ t ∉ Z.basicOpen σ) : SncChart A e (valR ζ W σ) := by
  obtain ⟨n, V, hcov, hV⟩ := hc
  obtain ⟨m, u, c, hsum, hl⟩ := exists_cover_basicOpen hW V hcov
  have hv : ∀ w : Γ(Z, W), valR ζ W w ∈ A := fun w => by
    have : valR ζ W w ∈ Set.range (valMap ζ W h).hom := by
      rw [valR_eq _ _ h]
      exact ⟨w, rfl⟩
    rw [hA] at this
    exact this
  refine ⟨m, fun l => valR ζ W (u l), fun l => valR ζ W (c l), fun l => hv _, fun l => hv _, ?_,
    fun l hf S hS => ?_⟩
  · simp only [valR_eq _ _ h]
    simp only [← map_mul, ← map_sum, hsum, map_one]
  · obtain ⟨j, v, huv⟩ := hl l
    obtain ⟨z, k, hk, hz, hT⟩ := hV j
    exact snc_on_basicOpen ζ g e T hsm hW h A hA σ hσ (u l) hf (V j).2 v huv z k hk hz hT S hS

end GlobalTheory.CompanionTheory.Ar.SncRes
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncPointsTransferDominating
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PatchIso

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem unitAt_congr {X' : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω) ⟶ X'}
    {p : Cpt ξ} {p' : Cpt ξ'} (h : regAt ξ' p' = regAt ξ p) (a : Ω) : unitAt ξ' p' a ↔ unitAt ξ p a := by
  unfold unitAt
  rw [h]

theorem char_zero_congr {X' : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω) ⟶ X'}
    {p : Cpt ξ} {p' : Cpt ξ'} (h : regAt ξ' p' = regAt ξ p) (hp : Char0 ξ p) : Char0 ξ' p' := fun r hr hf =>
  hp r hr fun hu => hf ((unitAt_congr h _).2 hu)

theorem mem_genFib_of_char0 [CharZero Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : Cpt ξ} (hp : Char0 ξ p) :
    p ∈ genFib ξ := by
  have key : ∀ n : ℕ, 0 < n → ((n : Ω))⁻¹ ∈ regAt ξ p := by
    intro n
    induction n using induction_on_primes with
    | zero => exact fun h => absurd h (lt_irrefl 0)
    | one => intro _; simpa using (regAt ξ p).one_mem
    | prime_mul r a hr ih =>
      intro h
      have ha : 0 < a := Nat.pos_of_mul_pos_left h
      have hu : unitAt ξ p (r : Ω) := not_not.1 (hp r hr)
      rw [Nat.cast_mul, mul_inv]
      exact mul_mem hu.2.2 (ih ha)
  exact fun n hn => ⟨Nat.cast_ne_zero.2 hn.ne', natCast_mem _ n, key n hn⟩

theorem exists_below [CharZero Ω] {X₁ X₂ : Scheme.{0}} {ξ₁ : Spec (CommRingCat.of Ω) ⟶ X₁}
    {ξ₂ : Spec (CommRingCat.of Ω) ⟶ X₂} {g : X₂ ⟶ X₁} (hg : IsCptGen ξ₂)
    (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ₂ ξ₁ g (RingHom.id Ω))
    (hi : ∀ q ∈ genFib ξ₁, IsoAt ξ₂ g (RingHom.id Ω) q) (p : Cpt ξ₂) (hp : Char0 ξ₂ p) :
    ∃ p₁ : Cpt ξ₁, p₁.1 = g p.1 ∧ Char0 ξ₁ p₁ ∧ regAt ξ₂ p = regAt ξ₁ p₁ := by
  obtain ⟨h, -, hu⟩ := RegAtDom.regAt_dominates X₁ Ω ξ₁ X₂ Ω ξ₂ g (RingHom.id Ω) hd p
  have c : Char0 ξ₁ ⟨g p.1, h⟩ := fun r hr hf =>
    hf (hu hg (r : Ω) (natCast_mem _ r) (not_not.1 (hp r hr)))
  refine ⟨⟨g p.1, h⟩, rfl, c, ?_⟩
  rw [(hi _ (mem_genFib_of_char0 c)).regAt_eq p rfl, Subring.map_id]

theorem exists_above [CharZero Ω] {X₁ X₂ : Scheme.{0}} {ξ₁ : Spec (CommRingCat.of Ω) ⟶ X₁}
    {ξ₂ : Spec (CommRingCat.of Ω) ⟶ X₂} {g : X₂ ⟶ X₁}
    (hi : ∀ q ∈ genFib ξ₁, IsoAt ξ₂ g (RingHom.id Ω) q) (p₁ : Cpt ξ₁) (hp : Char0 ξ₁ p₁) :
    ∃ p : Cpt ξ₂, g p.1 = p₁.1 ∧ Char0 ξ₂ p ∧ regAt ξ₂ p = regAt ξ₁ p₁ := by
  have I := hi p₁ (mem_genFib_of_char0 hp)
  obtain ⟨p, hp', -⟩ := I.existsUnique
  have e : regAt ξ₂ p = regAt ξ₁ p₁ := by rw [I.regAt_eq p hp', Subring.map_id]
  exact ⟨p, hp', char_zero_congr e hp, e⟩

theorem sncPts_of_isoAt :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] (κ₁ κ₂ : Type) (x₁ : κ₁ → Ω) (x₂ : κ₂ → Ω) (X₁ X₂ : Scheme.{0}) (ξ₁ : Sp Ω ⟶ X₁) (ξ₂ : Sp Ω ⟶ X₂) (g : X₂ ⟶ X₁) (e : ℕ) (Ab : Set X₁), (∀ q : X₁, genPt ξ₁ ⤳ q) → (∀ q : X₂, genPt ξ₂ ⤳ q) → CoordTie ℤ ξ₁ x₁ → CoordTie ℤ ξ₂ x₂ → GlobalTheory.CompanionTheory.Ar.Dominates ξ₂ ξ₁ g (RingHom.id Ω) → (∀ q ∈ genFib ξ₁, IsoAt ξ₂ g (RingHom.id Ω) q) → SncPts ξ₁ e {p | Char0 ξ₁ p ∧ p.1 ∉ Ab} → SncPts ξ₂ e {p | Char0 ξ₂ p ∧ g p.1 ∉ Ab} := by
  intro Ω _ _ κ₁ κ₂ x₁ x₂ X₁ X₂ ξ₁ ξ₂ g e Ab _ _ _ t₂ hd hi hs p hp
  have ePts : Pts ξ₂ = Pts ξ₁ := by
    ext R
    constructor
    · rintro ⟨p₂, c, rfl⟩
      obtain ⟨p₁, -, c₁, r⟩ := exists_below t₂.gen hd hi p₂ c
      exact ⟨p₁, c₁, r⟩
    · rintro ⟨p₁, c, rfl⟩
      obtain ⟨p₂, -, c₂, r⟩ := exists_above hi p₁ c
      exact ⟨p₂, c₂, r.symm⟩
  have eB : regAt ξ₂ '' {p | Char0 ξ₂ p ∧ g p.1 ∉ Ab} = regAt ξ₁ '' {p | Char0 ξ₁ p ∧ p.1 ∉ Ab} := by
    ext R
    constructor
    · rintro ⟨p₂, ⟨c, ha⟩, rfl⟩
      obtain ⟨p₁, e₁, c₁, r⟩ := exists_below t₂.gen hd hi p₂ c
      exact ⟨p₁, ⟨c₁, e₁ ▸ ha⟩, r.symm⟩
    · rintro ⟨p₁, ⟨c, ha⟩, rfl⟩
      obtain ⟨p₂, e₂, c₂, r⟩ := exists_above hi p₁ c
      exact ⟨p₂, ⟨c₂, by rwa [e₂]⟩, r⟩
  obtain ⟨p₁, -, c₁, r⟩ := exists_below t₂.gen hd hi p hp
  obtain ⟨A, z, n, q, hP, hq, hl⟩ := hs p₁ c₁
  refine ⟨A, z, n, q, ?_, hq, ?_⟩
  · rw [ePts, eB]
    exact hP
  · rw [r]
    exact hl

end GlobalTheory.CompanionTheory.Ar.PatchIso
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.StandardSmoothBasicOpen
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncRes

theorem hom_to_spQ_ext {X : Scheme.{0}} (a b : X ⟶ Sp ℚ) : a = b := by
  haveI : IsAffine (Sp ℚ) := inferInstanceAs (IsAffine (Spec (CommRingCat.of ℚ)))
  apply ext_of_isAffine
  apply (cancel_epi (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv).mp
  apply CommRingCat.hom_ext
  exact RingHom.ext_rat _ _

theorem smoothOfRelativeDimension_spMap (B : Type) [CommRing B] [Algebra ℚ B] (e : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension e ℚ B] :
    SmoothOfRelativeDimension e (spMap (algebraMap ℚ B)) := by
  show SmoothOfRelativeDimension e (Spec.map (CommRingCat.ofHom (algebraMap ℚ B)))
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension e)]
  exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
    ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap e).mpr inferInstance)

def valEquiv {Ω : Type} [Field Ω] [CharZero Ω] {Z : Scheme.{0}} (ζ : Sp Ω ⟶ Z) [IsDominant ζ] [IsReduced Z]
    (W : Z.Opens) (h : ⊤ ≤ ζ ⁻¹ᵁ W) (A : Subalgebra ℚ Ω) (hA : Set.range (valMap ζ W h).hom = A) :
    Γ(Z, W) ≃+* A :=
  RingEquiv.ofBijective
    ((valMap ζ W h).hom.codRestrict A.toSubring (fun x => by
      have : (valMap ζ W h).hom x ∈ (A : Set Ω) := hA ▸ Set.mem_range_self x
      exact this))
    ⟨fun x y hxy => valMap_injective ζ h (congrArg Subtype.val hxy), fun y => by
      have : (y : Ω) ∈ Set.range (valMap ζ W h).hom := hA ▸ y.2
      obtain ⟨x, hx⟩ := this
      exact ⟨x, Subtype.ext hx⟩⟩

theorem smoothOfRelativeDimension_basicOpen_of_away : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (Z : Scheme.{0}) (ζ : Sp Ω ⟶ Z) [IsDominant ζ] [IsReduced Z] (g : Z ⟶ Sp ℚ) (e : ℕ) (W : Z.Opens) (hW : IsAffineOpen W) (h : ⊤ ≤ ζ ⁻¹ᵁ W) (A : Subalgebra ℚ Ω) (hA : Set.range (valMap ζ W h).hom = A) (σ : Γ(Z, W)) (g₀ : A) (hg : (g₀ : Ω) = valR ζ W σ) [Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away g₀)], SmoothOfRelativeDimension e ((Z.basicOpen σ).ι ≫ g) := by
  intro Ω _ _ Z ζ _ _ g e W hW h A hA σ g₀ hg _
  haveI := hW.isLocalization_basicOpen σ
  have hE : valEquiv ζ W h A hA σ = g₀ := by
    apply Subtype.ext
    rw [hg]
    show (valMap ζ W h).hom σ = valR ζ W σ
    simp only [valR, valMap, dif_pos h]
    rfl
  let ψ : Γ(Z, Z.basicOpen σ) ≃+* Localization.Away g₀ :=
    IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers σ) (T := Submonoid.powers g₀) _ _ (valEquiv ζ W h A hA)
      (by rw [Submonoid.map_powers]; exact congrArg Submonoid.powers hE)
  have hiso : IsIso (CommRingCat.ofHom (ψ.symm : Localization.Away g₀ →+* Γ(Z, Z.basicOpen σ))) :=
    ⟨⟨CommRingCat.ofHom (ψ : Γ(Z, Z.basicOpen σ) →+* Localization.Away g₀),
      by ext x; simp, by ext x; simp⟩⟩
  let f2 : Spec Γ(Z, Z.basicOpen σ) ⟶ Sp (Localization.Away g₀) :=
    Spec.map (CommRingCat.ofHom (ψ.symm : Localization.Away g₀ →+* Γ(Z, Z.basicOpen σ)))
  haveI : IsIso f2 := by dsimp only [f2]; infer_instance
  have key : (Z.basicOpen σ).ι ≫ g =
      ((hW.basicOpen σ).isoSpec.hom ≫ f2) ≫ spMap (algebraMap ℚ (Localization.Away g₀)) :=
    hom_to_spQ_ext _ _
  rw [key]
  haveI := smoothOfRelativeDimension_spMap (Localization.Away g₀) e
  have := smoothOfRelativeDimension_comp 0 e ((hW.basicOpen σ).isoSpec.hom ≫ f2)
    (spMap (algebraMap ℚ (Localization.Away g₀)))
  rwa [zero_add] at this

end GlobalTheory.CompanionTheory.Ar.SncRes
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentVectorLiftsOpenImmersionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_vector_lifts_open_immersion : ∀ (A T : Scheme.{0}) (φ : A ⟶ T) [IsOpenImmersion φ] (g : ℕ) (W : (Fin g → ℂ) → (Sp ℂ ⟶ A)) (y : Fin g → ℂ) (v : Sp (DualNumber ℂ) ⟶ T), IsDerivAt0 (fun x => W x ≫ φ) y v → ∃ v' : Sp (DualNumber ℂ) ⟶ A, v' ≫ φ = v ∧ IsDerivAt0 W y v' := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.DOpen.isDerivAt0_lift_of_isOpenImmersion | exact GlobalTheory.CompanionTheory.Ggeo.DOpen.isDerivAt0_lift_of_isOpenImmersion | (intros; apply GlobalTheory.CompanionTheory.Ggeo.DOpen.isDerivAt0_lift_of_isOpenImmersion <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TensorEquivOfBasisExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep

namespace GlobalTheory.CompanionTheory.Ar.FlagStep

theorem exists_tensor_equiv_of_semilinear :
    ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω] (V V' : Type) [AddCommGroup V]
    [Module Ω₀ V] [AddCommGroup V'] [Module Ω V'] (j : V →+ V'),
    (∀ (a : Ω₀) e, j (a • e) = algebraMap Ω₀ Ω a • j e) →
    (∀ (n : ℕ) (b : Fin n → V), LinearIndependent Ω₀ b → LinearIndependent Ω fun k => j (b k)) →
    Submodule.span Ω (Set.range j) = ⊤ →
    ∃ Φ : TensorProduct Ω₀ Ω V ≃ₗ[Ω] V', ∀ e, Φ (TensorProduct.mk Ω₀ Ω V 1 e) = j e := by
  intro Ω₀ Ω _ _ _ V V' _ _ _ _ j hsemi hind hspan
  letI : Module Ω₀ V' := Module.compHom V' (algebraMap Ω₀ Ω)
  haveI : IsScalarTower Ω₀ Ω V' := ⟨fun a b x => by
    change (a • b) • x = algebraMap Ω₀ Ω a • (b • x)
    rw [Algebra.smul_def, mul_smul]⟩
  let jl : V →ₗ[Ω₀] V' :=
    { toFun := j
      map_add' := j.map_add
      map_smul' := fun a e => hsemi a e }
  let L : TensorProduct Ω₀ Ω V →ₗ[Ω] V' := jl.liftBaseChange Ω
  have hL : ∀ e, L (TensorProduct.mk Ω₀ Ω V 1 e) = j e := by
    intro e
    change jl.liftBaseChange Ω (1 ⊗ₜ[Ω₀] e) = j e
    rw [LinearMap.liftBaseChange_tmul, one_smul]
    rfl
  have hsurj : Function.Surjective L := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨e, rfl⟩
    exact ⟨_, hL e⟩
  let B := Module.Basis.ofVectorSpace Ω₀ V
  let C := Algebra.TensorProduct.basis Ω B
  have hC : ∀ i, L (C i) = j (B i) := by
    intro i
    rw [Algebra.TensorProduct.basis_apply]
    exact hL (B i)
  have hli : LinearIndependent Ω (fun i => j (B i)) := by
    rw [linearIndependent_iff_finset_linearIndependent]
    intro s
    let e := s.equivFin
    have h1 : LinearIndependent Ω₀ (fun k : Fin s.card => B (e.symm k).1) :=
      B.linearIndependent.comp _ (Subtype.val_injective.comp e.symm.injective)
    have h2 := (hind _ _ h1).comp e e.injective
    convert h2 using 1
    funext x
    simp
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h0 : Finsupp.linearCombination Ω (fun i => j (B i)) (C.repr x) = 0 := by
      rw [← hx]
      conv_rhs => rw [← C.linearCombination_repr x]
      rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, map_finsuppSum]
      simp [hC]
    have h1 : C.repr x = 0 := hli (h0.trans (map_zero _).symm)
    simpa using h1
  exact ⟨LinearEquiv.ofBijective L ⟨hinj, hsurj⟩, fun e => hL e⟩

end GlobalTheory.CompanionTheory.Ar.FlagStep
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusKernelPrimeQuotientStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_kernel_prime_quotient : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsSeparated G.hom] (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (u : splitTorus S X ⟶ G) [IsMonHom u] (k : Type) [Field k] (b : Sp k ⟶ S) (M : LieModel (splitTorus S X) b (X →+ k)), IsCocharLie M → ∀ δ : X →+ k, δ ≠ 0 → M.pt δ ≫ u = 1 → ∃ (l : ℕ) (_ : l.Prime) (ψ : X →+ ZMod l), Function.Surjective ψ ∧ KillsOver u ψ.ker b := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TsField.exists_mu_killed | exact GlobalTheory.CompanionTheory.Ar.TsField.exists_mu_killed | (intros; apply GlobalTheory.CompanionTheory.Ar.TsField.exists_mu_killed <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerI5OfReferenceStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tower_i5_of_reference : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (II : IntersectionSystem) (R : T.Comp → RootModel Ψ N), IsIntersectionSystem II → HasRef T R → (∀ c, RefLower (R c)) → T.I5 II := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Ht.RefTower.i5_of_hasRef_of_refLower | exact GlobalTheory.CompanionTheory.Ar.Ht.RefTower.i5_of_hasRef_of_refLower | (intros; apply GlobalTheory.CompanionTheory.Ar.Ht.RefTower.i5_of_hasRef_of_refLower <;> assumption)
end


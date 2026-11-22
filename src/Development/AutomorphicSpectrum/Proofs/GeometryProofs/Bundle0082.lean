import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptIsoCompare
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0075
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0018
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0078
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0076
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0006

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptIsoCompareStatement
section
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_cpt_iso_compare : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β') (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (A : HodgeCpt Y S y) (A' : HodgeCpt Y' S y) (e : A'.X ≅ A.X) (φ : A.Li ≃ₗ[Ω] A'.Li) (Fl : A.Flag) (Fl' : A'.Flag) (τ τ' : CMType H) (i : Fin (D.p + D.q)) (e₀ e₀' : Ω) (L L' : HermLine ι), Birational y → A'.ξ ≫ e.hom = A.ξ → (∀ (q : Cpt A'.ξ) (h : genPt A.ξ ⤳ e.hom q.1) (v : A.Li), (v ∈ A.V (.inl τ) ⟨e.hom q.1, h⟩ ↔ φ v ∈ A'.V (.inl τ') q) ∧ (v ∈ A.V (.inr τ) ⟨e.hom q.1, h⟩ ↔ φ v ∈ A'.V (.inr τ') q)) → (∀ k, (flagStep Ω (Fl.b (.inl τ)) k).map (φ : A.Li →ₗ[Ω] A'.Li) = flagStep Ω (Fl'.b (.inl τ')) k ∧ (flagStep Ω (Fl.b (.inr τ)) k).map (φ : A.Li →ₗ[Ω] A'.Li) = flagStep Ω (Fl'.b (.inr τ')) k) → (∀ z : Sp ℂ ⟶ A'.X, (A'.Interior z ↔ A.Interior (z ≫ e.hom)) ∧ (A'.Interior z → ∀ (r : ℕ) (b : Fin r → A.Li) (Γ : Matrix (Fin r) (Fin r) ℂ), A.M.GramAt A.t.PP.L (z ≫ e.hom) b Γ ↔ A'.M.GramAt A'.t.PP.L z (fun i => φ (b i)) Γ)) → (Fl.rootLat (τ, i)).IsDegOn Set.univ y L.a e₀ → (Fl'.rootLat (τ', i)).IsDegOn Set.univ y L'.a e₀' → Fl.IsHodgeLine (τ, i) e₀ L → Fl'.IsHodgeLine (τ', i) e₀' L' → (∀ (z : Sp ℂ ⟶ A.X), A.Interior z → ∀ s, ∃ (h : genPt A.ξ ⤳ centre z) (b : Fin (labelRk D s) → A.Li) (Γ : Matrix (Fin (labelRk D s)) (Fin (labelRk D s)) ℂ), (∀ k, flagStep Ω b k = flagStep Ω (Fl.b s) k) ∧ (A.V s).IsFrameAt b ⟨centre z, h⟩ ∧ A.M.GramAt A.t.PP.L z b Γ ∧ Γ.PosDef) → IsoLineOn (mCoordIdeal y) {w | ∃ z : Sp ℂ ⟶ A.X, CoordsAt A.ξ y z w ∧ A.Interior z} L L' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.RootIso.rootLine_iso | exact GlobalTheory.CompanionTheory.Ar.Cmp.RootIso.rootLine_iso | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.RootIso.rootLine_iso <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateDualEqOfOmegaEqStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_dual_eq_of_omega_eq : ∀ (E : Type) [Field E] [NumberField E] (s : 𝓞 E ≃+* 𝓞 E) (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G G' : Over X) [GrpObj G] [GrpObj G'] (L : LB G.left) (L' : LB G'.left) (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (M' : LieModel G' ξ V) (n n' : ℕ) (ρ : 𝓞 E →+* Module.End Ω V) (τ : 𝓞 E →+* Ω) (q : Cpt ξ), M'.htOm L' n' q = M.htOm L n q → M'.htDual L' n' (ρ.comp s.toRingHom) (τ.comp s.toRingHom) q = M.htDual L n ρ τ q ∧ M'.htW L' n' (ρ.comp s.toRingHom) (τ.comp s.toRingHom) (differentIdeal ℤ (𝓞 E)) q = M.htW L n ρ τ (differentIdeal ℤ (𝓞 E)) q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.htDual_htW_relabel | exact GlobalTheory.CompanionTheory.Ar.htDual_htW_relabel | (intros; apply GlobalTheory.CompanionTheory.Ar.htDual_htW_relabel <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsoLineOnEquivalenceStatement
section
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iso_line_on_equivalence : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (Xo : Set ((Σ k, ι k) → ℂ)), IsMultiProjPrime P → Xo ⊆ mcPts P → (∀ (J : Type) [Fintype J] (ℓ ℓ' : J → HermLine ι) (n : J → ℤ), (∀ j, IsoLineOn P Xo (ℓ j) (ℓ' j)) → IsoLineOn P Xo (Top.combLine ℓ n) (Top.combLine ℓ' n)) ∧ (∀ A B C : HermLine ι, IsoLineOn P Xo A B → IsoLineOn P Xo B C → IsoLineOn P Xo A C) ∧ (∀ A B : HermLine ι, IsoLineOn P Xo A B → IsoLineOn P Xo B A) ∧ ∀ (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)] (κ : K₁ → K) (v : (Σ k, ι₁ k) → Σ k, ι k) (J : Type) [Fintype J] (ℓ : J → HermLine ι₁) (ℓ' : J → HermLine ι) (n : J → ℤ), IsBlockMap κ v → (∀ j, IsPullHerm κ v (ℓ j) (ℓ' j)) → IsPullHerm κ v (Top.combLine ℓ n) (Top.combLine ℓ' n) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.IsoLines.isoLineOn_comb_trans_symm_pull | exact GlobalTheory.CompanionTheory.Ar.Cmp.IsoLines.isoLineOn_comb_trans_symm_pull | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.IsoLines.isoLineOn_comb_trans_symm_pull <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinCoordsCoordTieStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.join_coords_coordTie : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (κ' : Type) [Finite κ'] (w : κ' → Ω), (∀ p : Cpt M.ξ, ∃ l, InChart M.ξ w l p) → CoordTie o M.ξ (joinCo (RingHom.id Ω) x w) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Retie.coordTie_join_of_charts | exact GlobalTheory.CompanionTheory.Ar.Retie.coordTie_join_of_charts | (intros; apply GlobalTheory.CompanionTheory.Ar.Retie.coordTie_join_of_charts <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelBaseChangeActionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_base_change_action : ∀ (L L' : Type) [Field L] [Field L'] (e : L →+* L') (G : Over (Sp L)) (G' : Over (Sp L')) [GrpObj G] [GrpObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G (spMap e) φ → ∀ (O : Type) [CommRing O] (act : OAct O G) (act' : OAct O G'), (∀ a, (act'.act a).left ≫ φ = φ ≫ (act.act a).left) → ∀ (V V' : Type) [AddCommGroup V] [Module L V] [AddCommGroup V'] [Module L' V'] (MV : LieModel G (𝟙 (Sp L)) V) (MV' : LieModel G' (𝟙 (Sp L')) V') (j : V →+ V'), (∀ x, (MV'.pt (j x)).left ≫ φ = spMap (dualMap e) ≫ (MV.pt x).left) → Submodule.span L' (Set.range j) = ⊤ → ∀ ρ : O →+* Module.End L V, MV.IsActOf act.act ρ → ∃ ρ' : O →+* Module.End L' V', MV'.IsActOf act'.act ρ' ∧ ∀ a x, ρ' a (j x) = j (ρ a x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ActBC.exists_act_extends | exact GlobalTheory.CompanionTheory.Ar.ActBC.exists_act_extends | (intros; apply GlobalTheory.CompanionTheory.Ar.ActBC.exists_act_extends <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalizationsEqualBasicOpens
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase.CommonLoc

open Mdl

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem mem_of_isLocAt {A : Subalgebra ℚ Ω} {q : Ideal A} {R : Subring Ω} (hq : q.IsPrime)
    (hR : IsLocAt A q R) {a : Ω} (ha : a ∈ A) : a ∈ R :=
  (hR a).2 ⟨1, (Ideal.ne_top_iff_one q).1 hq.ne_top, by simpa using ha⟩

theorem unit_of_not_mem {A : Subalgebra ℚ Ω} {q : Ideal A} {R : Subring Ω}
    (hR : IsLocAt A q R) {a : A} (ha : a ∉ q) : (a : Ω) ≠ 0 ∧ (a : Ω)⁻¹ ∈ R := by
  have h0 : (a : Ω) ≠ 0 := fun h => ha (by
    have e : a = 0 := Subtype.ext h
    rw [e]
    exact q.zero_mem)
  exact ⟨h0, (hR _).2 ⟨a, ha, by rw [mul_inv_cancel₀ h0]; exact A.one_mem⟩⟩

theorem not_mem_of_unit {A : Subalgebra ℚ Ω} {q : Ideal A} {R : Subring Ω}
    (hR : IsLocAt A q R) {b : A} (h0 : (b : Ω) ≠ 0) (hi : (b : Ω)⁻¹ ∈ R) : b ∉ q := by
  obtain ⟨s, hs, hsb⟩ := (hR _).1 hi
  intro hb
  apply hs
  have e : s = ⟨_, hsb⟩ * b := Subtype.ext (by
    rw [Subalgebra.coe_mul]
    exact (inv_mul_cancel_right₀ h0 _).symm)
  rw [e]
  exact q.mul_mem_left _ hb

theorem invAdj_le_of {A C : Subalgebra ℚ Ω} {h : Ω} (hA : A ≤ C) (hh : h⁻¹ ∈ C) : invAdj A h ≤ C :=
  Algebra.adjoin_le (by
    rintro x (rfl | hx)
    · exact hh
    · exact hA hx)

theorem invAdj_le_mul {A : Subalgebra ℚ Ω} {g s : Ω} (hs : s ∈ A) (h0 : g * s ≠ 0) :
    invAdj A g ≤ invAdj A (g * s) := by
  refine invAdj_le_of (le_invAdj _ _) ?_
  have hs0 : s ≠ 0 := right_ne_zero_of_mul h0
  have hg0 : g ≠ 0 := left_ne_zero_of_mul h0
  have e : g⁻¹ = s * (g * s)⁻¹ := by field_simp
  rw [e]
  exact Subalgebra.mul_mem _ (le_invAdj _ _ hs) (inv_mem_invAdj _ _)

theorem exists_den {A B : Subalgebra ℚ Ω} {q : Ideal A} {R : Subring Ω} (hq : q.IsPrime)
    (hR : IsLocAt A q R) (hB : B.FG) (hBR : ∀ b ∈ B, b ∈ R) : ∃ g : A, g ∉ q ∧ B ≤ invAdj A g := by
  classical
  have key : ∀ T : Finset Ω, (∀ b ∈ T, b ∈ R) → ∃ g : A, g ∉ q ∧ ∀ b ∈ T, b ∈ invAdj A g := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact fun _ => ⟨1, (Ideal.ne_top_iff_one q).1 hq.ne_top, by simp⟩
    | insert b T _ ih =>
      intro hT
      obtain ⟨g₁, hg₁, hg₁T⟩ := ih fun x hx => hT x (Finset.mem_insert_of_mem hx)
      obtain ⟨s, hs, hsb⟩ := (hR b).1 (hT b (Finset.mem_insert_self _ _))
      have hmul : g₁ * s ∉ q := fun h => (hq.mem_or_mem h).elim hg₁ hs
      have h0 : (g₁ : Ω) * s ≠ 0 := (unit_of_not_mem hR hmul).1
      have hs0 : (s : Ω) ≠ 0 := right_ne_zero_of_mul h0
      have hg0 : (g₁ : Ω) ≠ 0 := left_ne_zero_of_mul h0
      refine ⟨g₁ * s, hmul, ?_⟩
      rw [Subalgebra.coe_mul]
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · have e : x = ((s : Ω) * x) * g₁ * ((g₁ : Ω) * s)⁻¹ := by field_simp
        rw [e]
        exact Subalgebra.mul_mem _
          (Subalgebra.mul_mem _ (le_invAdj _ _ hsb) (le_invAdj _ _ g₁.2)) (inv_mem_invAdj _ _)
      · exact invAdj_le_mul s.2 h0 (hg₁T x hx)
  obtain ⟨S, rfl⟩ := hB
  obtain ⟨g, hg, hgS⟩ := key S fun b hb => hBR b (Algebra.subset_adjoin hb)
  exact ⟨g, hg, Algebra.adjoin_le fun b hb => hgS b hb⟩

theorem exists_clear {A B : Subalgebra ℚ Ω} {q : Ideal A} {q' : Ideal B} {R : Subring Ω}
    (hR : IsLocAt A q R) (hR' : IsLocAt B q' R) {g : A} {h : B} (hg : g ∉ q) (hh : h ∉ q')
    (hgh : (g : Ω) ∈ invAdj B h) : ∃ (a : B) (m : ℕ), a ∉ q' ∧ (a : Ω) = g * (h : Ω) ^ m := by
  obtain ⟨gn, gi⟩ := unit_of_not_mem hR hg
  obtain ⟨hn, hi⟩ := unit_of_not_mem hR' hh
  obtain ⟨m, hm⟩ := exists_mul_pow_mem h.2 hn hgh
  refine ⟨⟨_, hm⟩, m, not_mem_of_unit hR' (mul_ne_zero gn (pow_ne_zero _ hn)) ?_, rfl⟩
  show ((g : Ω) * (h : Ω) ^ m)⁻¹ ∈ R
  rw [mul_inv, ← inv_pow]
  exact R.mul_mem gi (R.pow_mem hi _)

theorem exists_common_loc : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A B : Subalgebra ℚ Ω) (q : Ideal A) (q' : Ideal B)
    (R : Subring Ω), A.FG → B.FG → q.IsPrime → q'.IsPrime → IsLocAt A q R → IsLocAt B q' R →
    ∃ (g : A) (h : B), g ∉ q ∧ h ∉ q' ∧ Mdl.invAdj A g = Mdl.invAdj B h := by
  intro Ω _ _ A B q q' R hA hB hq hq' hR hR'
  obtain ⟨g₀, hg₀, hBg⟩ := exists_den hq hR hB fun b hb => mem_of_isLocAt hq' hR' hb
  obtain ⟨h₀, hh₀, hAh⟩ := exists_den hq' hR' hA fun b hb => mem_of_isLocAt hq hR hb
  obtain ⟨a, m, ha, ea⟩ := exists_clear hR hR' hg₀ hh₀ (hAh g₀.2)
  obtain ⟨h, hh, eh⟩ : ∃ h : B, h ∉ q' ∧ (h : Ω) = h₀ * a :=
    ⟨h₀ * a, fun hm => (hq'.mem_or_mem hm).elim hh₀ ha, rfl⟩
  obtain ⟨a', l, ha', ea'⟩ := exists_clear hR' hR hh hg₀ (hBg h.2)
  obtain ⟨g, hg, eg⟩ : ∃ g : A, g ∉ q ∧ (g : Ω) = g₀ * a' :=
    ⟨g₀ * a', fun hm => (hq.mem_or_mem hm).elim hg₀ ha', rfl⟩
  have g0n := (unit_of_not_mem hR hg₀).1
  have h0n := (unit_of_not_mem hR' hh₀).1
  have gn := (unit_of_not_mem hR hg).1
  have hn := (unit_of_not_mem hR' hh).1
  have an := (unit_of_not_mem hR' ha).1
  have an' := (unit_of_not_mem hR ha').1
  refine ⟨g, h, hg, hh, ?_⟩

  have hAh' : invAdj B (h₀ : Ω) ≤ invAdj B h := by
    rw [eh]
    exact invAdj_le_mul a.2 (eh ▸ hn)
  have hBg' : invAdj A (g₀ : Ω) ≤ invAdj A g := by
    rw [eg]
    exact invAdj_le_mul a'.2 (eg ▸ gn)
  have g0inv : (g₀ : Ω)⁻¹ ∈ invAdj B h := by
    have e : (g₀ : Ω)⁻¹ = (h₀ : Ω) ^ m * h₀ * (h : Ω)⁻¹ := by
      rw [eh, ea]
      field_simp
    rw [e]
    exact Subalgebra.mul_mem _
      (Subalgebra.mul_mem _ (le_invAdj _ _ (B.pow_mem h₀.2 _)) (le_invAdj _ _ h₀.2)) (inv_mem_invAdj _ _)
  have C1 : invAdj A (g₀ : Ω) ≤ invAdj B h := invAdj_le_of (hAh.trans hAh') g0inv
  have hinv : (h : Ω)⁻¹ ∈ invAdj A g := by
    have e : (h : Ω)⁻¹ = (g₀ : Ω) ^ l * g₀ * (g : Ω)⁻¹ := by
      rw [eg, ea']
      field_simp
    rw [e]
    exact Subalgebra.mul_mem _
      (Subalgebra.mul_mem _ (le_invAdj _ _ (A.pow_mem g₀.2 _)) (le_invAdj _ _ g₀.2)) (inv_mem_invAdj _ _)
  have ginv : (g : Ω)⁻¹ ∈ invAdj B h := by
    have e : (g : Ω)⁻¹ = (g₀ : Ω)⁻¹ * ((h : Ω)⁻¹ * ((g₀ : Ω)⁻¹) ^ l) := by
      rw [eg, ea', mul_inv, mul_inv, inv_pow]
    rw [e]
    exact Subalgebra.mul_mem _ g0inv
      (Subalgebra.mul_mem _ (inv_mem_invAdj _ _) (Subalgebra.pow_mem _ g0inv _))
  exact le_antisymm (invAdj_le_of ((le_invAdj A _).trans C1) ginv)
    (invAdj_le_of (hBg.trans hBg') hinv)

end GlobalTheory.CompanionTheory.Ar.SncBase.CommonLoc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogHermitianSumBoundedStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_hermitian_sum_bounded : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (J : Type) (A : HermLine ι) (B : J → HermLine ι) (T : Finset J), IsSmoothHerm A → (∀ j, IsSmoothHerm (B j)) → A.a = -∑ j ∈ T, (B j).a → ∃ C : ℝ, ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ a, z ⟨k, a⟩ ≠ 0) → |Real.log (A.h z) + ∑ j ∈ T, Real.log ((B j).h z)| ≤ C := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CancelBound.log_metrics_bounded | exact GlobalTheory.CompanionTheory.Ar.CancelBound.log_metrics_bounded | (intros; apply GlobalTheory.CompanionTheory.Ar.CancelBound.log_metrics_bounded <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelOverRamifiedExtensionStatement
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_over_ramified_extension : ∀ (O O' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] (ϖ : O) (ϖ' : O') (u : O'ˣ) (e : ℕ), Irreducible ϖ → Irreducible ϖ' → 0 < e → algebraMap O O' ϖ = u * ϖ' ^ e → ∀ (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MvPolynomial (Σ k, J k) O)) (d : ℕ), IsModelOver P d → IsModelOver (P.map (MvPolynomial.map (algebraMap O O'))) d → ∀ (a : K → ℕ) (f : MvPolynomial (Σ k, J k) O), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog f a → f ∉ P → ∀ l : List (K → ℤ), l.length = d → cycList (divCycle (P.map (MvPolynomial.map (algebraMap O O'))) (MvPolynomial.map (algebraMap O O') f)) l = e * cycList (divCycle P f) l := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.numbers_divCycle_baseChange_dvr | exact GlobalTheory.CompanionTheory.Ar.Num.numbers_divCycle_baseChange_dvr | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.numbers_divCycle_baseChange_dvr <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MultihomogCoveringFormsStatement
section
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multihomog_covering_forms : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (a b : K → ℕ) (n : ℕ) (u v : Fin n → MvPolynomial (Σ k, ι k) ℤ), (∀ j, GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (u j) a) → (∀ j, GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (v j) b) → (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ j, eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j)) ≠ 0) → (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ j, eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j)) ≠ 0) → ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm A → ReciprocityTheory.ChartRestriction.G.Geo.IsConjInvariantH A → ∃ A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, A'.a = (fun k => A.a k + (a k : ℤ) - (b k : ℤ)) ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm A' ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsConjInvariantH A' ∧ ∀ z : ((Σ k, ι k) → ℂ), A'.h z = A.h z * Real.sqrt ((∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j))‖ ^ 2) / (∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j))‖ ^ 2)) := by
  first | exact @GlobalTheory.CompanionTheory.TwistLine.twisted_hermitian_line | exact GlobalTheory.CompanionTheory.TwistLine.twisted_hermitian_line | (intros; apply GlobalTheory.CompanionTheory.TwistLine.twisted_hermitian_line <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MultihomogRatioInductionStatement
section
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multihomog_ratio_induction : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Q : (K → ℕ) → (K → ℕ) → MvPolynomial (Σ k, ι k) ℤ → MvPolynomial (Σ k, ι k) ℤ → Prop) (bf bg : K → ℕ), (∀ (a b d : K → ℕ) (u v m : MvPolynomial (Σ k, ι k) ℤ), Q a b u v → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog m d → Q (a + d) (b + d) (u * m) (v * m)) → (∀ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ), Q a b u v → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog u a ∧ GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog v b ∧ a + bf = b + bg) → (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ), Q a b u v ∧ eval z (MvPolynomial.map (Int.castRingHom ℂ) u) ≠ 0) → (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ), Q a b u v ∧ eval z (MvPolynomial.map (Int.castRingHom ℂ) v) ≠ 0) → ∃ (A B : K → ℕ) (n : ℕ) (u v : Fin n → MvPolynomial (Σ k, ι k) ℤ), A + bf = B + bg ∧ (∀ j, Q A B (u j) (v j)) ∧ (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ j, eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j)) ≠ 0) ∧ (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ j, eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j)) ≠ 0) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TwistLine.finite_pairs_common_bidegree | exact GlobalTheory.CompanionTheory.Ar.TwistLine.finite_pairs_common_bidegree | (intros; apply GlobalTheory.CompanionTheory.Ar.TwistLine.finite_pairs_common_bidegree <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalAffineChartExistsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normal_affine_chart_exists : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → Flat.NormalCpt ξ → ∀ q : Cpt ξ, ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (x : Spec (CommRingCat.of R) ⟶ X) (κ : FractionRing R ≃+* Ω), IsNoetherianRing R ∧ IsIntegrallyClosed R ∧ IsOpenImmersion x ∧ q.1 ∈ Set.range x ∧ (∀ y ∈ Set.range x, genPt ξ ⤳ y) ∧ spMap (κ.toRingHom.comp (algebraMap R _)) ≫ x = ξ := by
  first | exact @GlobalTheory.CompanionTheory.Relay.normal_affine_chart_exists | exact GlobalTheory.CompanionTheory.Relay.normal_affine_chart_exists | (intros; apply GlobalTheory.CompanionTheory.Relay.normal_affine_chart_exists <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalCptIffNormalSchemeStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normal_cpt_iff_normal_scheme : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), IsCptGen ξ → (∀ q : X, GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ q) → IsIntegral X ∧ (Flat.NormalCpt ξ ↔ IsNormalScheme X) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.XR.component_whole_isIntegral_and_normal | exact GlobalTheory.CompanionTheory.Ar.XR.component_whole_isIntegral_and_normal | (intros; apply GlobalTheory.CompanionTheory.Ar.XR.component_whole_isIntegral_and_normal <;> assumption)
end


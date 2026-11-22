import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0100
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0024
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0032
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0099
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGeneric
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0057
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0039
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0045
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0102
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0093
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinModelPointsProject
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.WeilBound.CoreStatements.AmpleLineBundles.LineHtInvariantBaseChangeScaling
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SubstitutionBilinearFormTransform
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0096

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermJetPointComposition
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc.JetPts

section
variable {X0 : Scheme.{0}} {k : Type} [Field k] (x : Sp k ⟶ X0)

theorem homAt_comp_homAt {A B C : Type} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] [CommRing C] [Algebra k C]
    (g : A →ₐ[k] B) (f : B →ₐ[k] C) : homAt x f ≫ homAt x g = homAt x (f.comp g) := by
  apply Over.OverMorphism.ext
  simp only [homAt, Over.comp_left, Over.homMk_left, spMap]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem homAt_id_eq {A : Type} [CommRing A] [Algebra k A] : homAt x (AlgHom.id k A) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  simp only [homAt, Over.homMk_left, spMap]
  exact Spec.map_id _

def trJ (κ : Type) {n M : ℕ} (h : n ≤ M) : Jet k κ M →ₐ[k] Jet k κ n :=
  Ideal.Quotient.factorₐ k (Ideal.pow_le_pow_right (by omega))

theorem trJ_mk (κ : Type) {n M : ℕ} (h : n ≤ M) (P : MvPolynomial κ k) :
    trJ (k := k) κ h (Ideal.Quotient.mk _ P) = Ideal.Quotient.mk _ P := rfl

theorem x_eq_of_trunc {Y : Over X0} {κ : Type} (z : ∀ m, overAt x (Jet k κ m) ⟶ Y)
    (hz : ∀ m, homAt x (jetTrunc : Jet k κ (m + 1) →ₐ[k] Jet k κ m) ≫ z (m + 1) = z m) {n M : ℕ} (h : n ≤ M) :
    homAt x (trJ κ h) ≫ z M = z n := by
  induction M, h using Nat.le_induction with
  | base =>
    have e : trJ (k := k) κ (le_refl n) = AlgHom.id k _ := by
      apply Ideal.Quotient.algHom_ext
      apply MvPolynomial.algHom_ext
      intro i
      rfl
    rw [e, homAt_id_eq, Category.id_comp]
  | succ M h ih =>
    have e : (trJ (k := k) κ (Nat.le_succ_of_le h)) = (trJ κ h).comp jetTrunc := by
      apply Ideal.Quotient.algHom_ext
      apply MvPolynomial.algHom_ext
      intro i
      rfl
    rw [← ih, ← hz M, e, ← homAt_comp_homAt, Category.assoc]

end

section
variable {k : Type} [Field k] {d : ℕ}

theorem liftJet_mk_eq {κ B : Type} [CommRing B] [Algebra k B] {n : ℕ} (f : MvPolynomial κ k →ₐ[k] B)
    (h : Ideal.span (Set.range fun i => f (MvPolynomial.X i)) ^ (n + 1) = ⊥) (P : MvPolynomial κ k) :
    liftJet f h (Ideal.Quotient.mk _ P) = f P := rfl

theorem jetMap_mk_eq {κ κ' : Type} {n : ℕ} (φ : κ → MvPolynomial κ' k) (hφ : ∀ i, φ i ∈ orig k κ') (P : MvPolynomial κ k) :
    (jetMap φ hφ : Jet k κ n →ₐ[k] Jet k κ' n) (Ideal.Quotient.mk _ P) = Ideal.Quotient.mk _ (MvPolynomial.aeval φ P) := rfl

theorem jq_mk_zero (w : Fin d → k) (p m : ℕ) (j : Fin d) :
    jq w p m (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 2), j))) =
      algebraMap k _ (w j) * dQ (Jet k (Fin 1 × Fin d) m) p := by
  rw [jq, liftJet_mk_eq]
  simp

theorem jq_mk_one (w : Fin d → k) (p m : ℕ) (j : Fin d) :
    jq w p m (Ideal.Quotient.mk _ (MvPolynomial.X ((1 : Fin 2), j))) =
      inR (k := k) (Jet k (Fin 1 × Fin d) m) p (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j))) := by
  rw [jq, liftJet_mk_eq]
  simp

theorem inL_mk (B : Type) [CommRing B] [Algebra k B] (p : ℕ) :
    inL (k := k) B p (Ideal.Quotient.mk _ (MvPolynomial.X ())) = dQ B p := by
  rw [inL, liftJet_mk_eq]
  simp

theorem ring_zero (w : Fin d → k) (p m : ℕ) :
    (jq w p m).comp (jetCopy d (p + m + 1) (0 : Fin 2)) =
      (inL (k := k) (Jet k (Fin 1 × Fin d) m) p).comp
        ((jetSubstP p fun q : Fin 1 × Fin d => MvPolynomial.C (w q.2) * MvPolynomial.X ()).comp
          (trJ (Fin 1 × Fin d) (show p ≤ p + m + 1 by omega))) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  rintro ⟨a, j⟩
  have ha : a = 0 := Subsingleton.elim _ _
  subst ha
  have h1 : jetCopy (S := k) d (p + m + 1) (0 : Fin 2) (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j))) =
      Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 2), j)) := by
    rw [jetCopy, jetMap_mk_eq]
    simp
  have h2 : jetSubstP (S := k) p (fun q : Fin 1 × Fin d => MvPolynomial.C (w q.2) * MvPolynomial.X ())
      (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j))) =
      algebraMap k _ (w j) * Ideal.Quotient.mk _ (MvPolynomial.X ()) := by
    rw [jetSubstP, jetMap_mk_eq]
    simp only [MvPolynomial.aeval_X, map_mul, MvPolynomial.constantCoeff_C, MvPolynomial.constantCoeff_X, mul_zero,
      map_zero, sub_zero]
    rfl
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, trJ_mk, h1, h2, jq_mk_zero, map_mul, AlgHom.commutes, inL_mk]

theorem ring_one (w : Fin d → k) (p m : ℕ) :
    (jq w p m).comp (jetCopy d (p + m + 1) (1 : Fin 2)) =
      (inR (k := k) (Jet k (Fin 1 × Fin d) m) p).comp
        (trJ (Fin 1 × Fin d) (show m ≤ p + m + 1 by omega)) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  rintro ⟨a, j⟩
  have ha : a = 0 := Subsingleton.elim _ _
  subst ha
  have h1 : jetCopy (S := k) d (p + m + 1) (1 : Fin 2) (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j))) =
      Ideal.Quotient.mk _ (MvPolynomial.X ((1 : Fin 2), j)) := by
    rw [jetCopy, jetMap_mk_eq]
    simp
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, trJ_mk, h1, jq_mk_one]

end

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (p : ℕ) (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d) (w : Fin d → k) (m : ℕ), homAt x (jq w p m) ≫ jptG t x d g.x (p + m + 1) (0 : Fin 2) = homAt x (inL (k := k) (Jet k (Fin 1 × Fin d) m) p) ≫ homAt x (jetSubstP p fun q : Fin 1 × Fin d => MvPolynomial.C (w q.2) * MvPolynomial.X ()) ≫ g.x p ∧ homAt x (jq w p m) ≫ jptG t x d g.x (p + m + 1) (1 : Fin 2) = homAt x (inR (k := k) (Jet k (Fin 1 × Fin d) m) p) ≫ g.x m := by
  intro E _ _ _ H _ X0 t k _ p x d g w m
  constructor
  · have hx := x_eq_of_trunc x g.x g.chart.trunc (show p ≤ p + m + 1 by omega)
    show homAt x (jq w p m) ≫ homAt x (jetCopy d (p + m + 1) (0 : Fin 2)) ≫ g.x (p + m + 1) = _
    rw [← hx, ← Category.assoc, homAt_comp_homAt, ring_zero, ← homAt_comp_homAt, ← homAt_comp_homAt]
    simp only [Category.assoc]
  · have hx := x_eq_of_trunc x g.x g.chart.trunc (show m ≤ p + m + 1 by omega)
    show homAt x (jq w p m) ≫ homAt x (jetCopy d (p + m + 1) (1 : Fin 2)) ≫ g.x (p + m + 1) = _
    rw [← hx, ← Category.assoc, homAt_comp_homAt, ring_one, ← homAt_comp_homAt]
    simp only [Category.assoc]

end GlobalTheory.CompanionTheory.Ar.Coc.JetPts
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentTwistFrameCompatStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_component_twist_frame_compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F)
    (Y : Model Xo c β) (Y' : Model Xo c β') (g : HostAut H) (Φ : Xo.X ≅ Xo.X)
    (n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K]
    (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y) (A' : HodgeCpt Y' S y)
    (e : A'.X ≅ A.X) (x x' : Sp Ω ⟶ Xo.XF c),
    Mono (spMap β) → Mono (spMap β') → Φ.hom ≫ Xo.s = Xo.s → A'.ξ ≫ e.hom = A.ξ → A.ξ ≫ A.f = x ≫ Y.j → A'.ξ ≫ A'.f = x' ≫ Y'.j →
    x' ≫ pullback.fst _ _ = x ≫ pullback.fst _ _ ≫ Φ.hom → x' ≫ pullback.snd _ _ = x ≫ pullback.snd _ _ →
    A.cst = A'.cst → x ≫ pullback.snd _ _ = spMap A.cst → (∀ p ∈ S, A'.R p = A.R p) →
    ∀ z : Sp ℂ ⟶ A'.X, A'.Interior z ↔ A.Interior (z ≫ e.hom) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TwistInterior.interior_iff | exact GlobalTheory.CompanionTheory.Ar.TwistInterior.interior_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.TwistInterior.interior_iff <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptBlockRefinement
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem HodgeCpt.Flag.exists_recoord_rootLines : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag), ∃ (K' : Type) (_ : Fintype K') (J' : K' → Type) (_ : ∀ k, Fintype (J' k)) (y' : (Σ k, J' k) → Ω) (κ : K → K') (v : ∀ k, J k ≃ J' (κ k)) (tie' : CoordTie ℤ 𝔐.ξ fun c' : (k : K') → J' k => ∏ k, y' ⟨k, c' k⟩) (xdeg : CMType H × Fin (D.p + D.q) → K' → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω), Function.Injective κ ∧ (∀ k i, y' ⟨κ k, v k i⟩ = y ⟨k, i⟩) ∧ ∀ r, (Fl.rootLat r).IsDegOn Set.univ y' (xdeg r) (e r) := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 Fl
  classical
  haveI : Fintype (CMType H) := Fintype.ofFinite _
  have hlin : ∀ s, LinearIndependent Ω (Fl.b s) := by
    intro s
    letI := 𝔐.fn.toAlgebra
    obtain ⟨_, _, _, _, _, h4, _⟩ := Fl.generic
    exact h4 s
  have hgr : ∀ s i, ((𝔐.V s).gr (Fl.b s) i).IsVBOn Set.univ 1 ⊤ := fun s i =>
    (Lat.IsFlagVBOn.isVBOn_gr_inter _ _ _ _ _ _ _ (Fl.b s) (hlin s) (Fl.sub s)).2.1 i
  have hroot : ∀ r, (Fl.rootLat r).IsVB 1 ⊤ := fun r =>
    (GlobalTheory.T.lattice_tensor_power_line_bundle _ _ _ Unit _ Set.univ (fun _ => hgr _ _) _).1
  obtain ⟨K', fK, J', fJ, y', κ, v, hκ, hv, tie', h⟩ :=
    GlobalTheory.T.exists_block_refinement_lines 𝔐.X Ω 𝔐.ξ K J y (CMType H × Fin (D.p + D.q)) Fl.rootLat 𝔐.tie hroot
  choose xdeg e hdeg using h
  exact ⟨K', fK, J', fJ, y', κ, v, tie', xdeg, e, hκ, hv, hdeg⟩

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGenericStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_cpt_interior_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y), Function.Injective β → 𝔐.Interior 𝔐.ξ ∧ (∃ x : Sp Ω ⟶ Xo.XF c, 𝔐.ξ ≫ 𝔐.f = x ≫ Y.j) ∧ CharZero Ω ∧ Function.Injective 𝔐.emb ∧ (∀ s, Module.finrank Ω (𝔐.Vgen s) = labelRk D s) ∧ (⨆ s, 𝔐.Vgen s) = ⊤ ∧ iSupIndep 𝔐.Vgen ∧ ∀ s a (q : Cpt 𝔐.ξ), 𝔐.emb s a ∈ regAt 𝔐.ξ q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeCpt.basic | exact GlobalTheory.CompanionTheory.Ar.HodgeCpt.basic | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeCpt.basic <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicFamilyConjugateStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.NineStatements GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_family_conjugate : ∀ (X : Scheme.{0}) (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)), IsHolTo B y → IsHolTo (star ⁻¹' B) (fun b => spMap (starRingEnd ℂ) ≫ y (star b)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.isHolTo_conj | exact GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.isHolTo_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.isHolTo_conj <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionFamilyFlatTwist
section
noncomputable section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem hermLine_eq_of_a_h {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {A B : HermLine ι}
    (ha : A.a = B.a) (hh : A.h = B.h) : A = B := by
  cases A
  cases B
  simp_all

theorem exists_tensorPow_last {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} (hI : IsIntersectionFamily I)
    {W : Ideal (MRing ι)} {n : ℕ} {L : Fin n → HermLine ι} (hW : IsArithVar W (n + 1))
    (hL : ∀ j, IsSmoothHerm (L j)) {B : HermLine ι} (hB : IsSmoothHerm B) {m : ℕ} (hm : 1 ≤ m) :
    ∃ C : HermLine ι, IsSmoothHerm C ∧ (∀ k, C.a k = m * B.a k) ∧ (∀ z, C.h z = B.h z ^ m) ∧
      I W (n + 1) (Fin.snoc L C) = m * I W (n + 1) (Fin.snoc L B) := by
  induction m, hm using Nat.le_induction with
  | base => exact ⟨B, hB, by simp, by simp, by simp⟩
  | succ m hm ih =>
    obtain ⟨C, hC, ha, hh, hi⟩ := ih
    refine ⟨C.tensor B, ContDiffOn.mul hC hB, fun k => ?_, fun z => ?_, ?_⟩
    · simp only [HermLine.tensor, Pi.add_apply, ha]
      push_cast
      ring
    · simp only [HermLine.tensor, hh, pow_succ]
    · rw [hI.2.1 W n L C B hW hL hC hB, hi]
      push_cast
      ring

theorem IsUnitSec.mono {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P W : Ideal (MRing ι)}
    {f g : MRing ι} (h : IsUnitSec P f g) (hPW : P ≤ W) : IsUnitSec W f g := by
  intro W' h1 h2 h3
  obtain ⟨a, b, ha, hb, hab⟩ := h W' h1 (hPW.trans h2) h3
  exact ⟨a, b, ha, hb, hPW hab⟩

theorem FlatHerm.inter_eq_neg_integral : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type)
    [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω)
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (W : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (A : HermLine ι) (S : FlatHerm y φ A) (d : ℕ) (u : ((Σ k, ι k) → ℂ) → ℝ),
    IsIntersectionFamily I → IsArithVar (mCoordIdeal y) d → OverInt y φ → mCoordIdeal y ≤ W →
    IsArithVar W (n + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A →
    IsPlaceWeight y φ (fun σ => Real.log (S.κ σ)) u →
    I W (n + 1) (Fin.snoc L A) = -ptsIntegral W (pot L) u := by
  intro K _ ι _ Ω _ F _ _ y φ I W n L A S d u hI hP hY hPW hW hL hA hu
  have hnu : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → (fun z => -u z) (fun p => c p.1 * z p) = (fun z => -u z) z :=
    fun c z hc => by simp only [hu.inv c z hc]

  set B : HermLine ι := A.tensor (HermLine.ofWeight (fun z => -u z) hnu) with hBdef
  have hBh : ∀ z, B.h z = A.h z * Real.exp (u z) := fun z => by
    simp [hBdef, HermLine.tensor, HermLine.ofWeight]
  have hBa : ∀ k, B.a k = A.a k := fun k => by
    simp [hBdef, HermLine.tensor, HermLine.ofWeight]
  have hexp : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => Real.exp (u z)) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
    Real.contDiff_exp.comp_contDiffOn hu.smooth
  have hB : IsSmoothHerm B := by
    have e : B.h = fun z => A.h z * Real.exp (u z) := funext hBh
    unfold IsSmoothHerm
    rw [e]
    exact ContDiffOn.mul hA hexp
  have hBA : B.tensor (HermLine.ofWeight u hu.inv) = A := by
    refine hermLine_eq_of_a_h ?_ ?_
    · funext k
      simp [HermLine.tensor, HermLine.ofWeight, hBa]
    · funext z
      have : (B.tensor (HermLine.ofWeight u hu.inv)).h z = B.h z * Real.exp (-u z) := rfl
      rw [this, hBh, mul_assoc, ← Real.exp_add]
      simp
  have hchange : I W (n + 1) (Fin.snoc L A) = I W (n + 1) (Fin.snoc L B) - ptsIntegral W (pot L) u := by
    have := metricChange K ι I hI W n L B u hu.inv hW hL hB hu.smooth
    rwa [hBA] at this

  obtain ⟨C, hC, hCa, hCh, hCI⟩ := exists_tensorPow_last hI hW hL hB (m := S.M) S.M_pos
  obtain ⟨f', g', df', dg', hf', hg', hdeg, hfW, hgW, -, hun, hnorm⟩ :=
    GlobalTheory.T.flat_herm_unit_section_avoid K ι Ω F y φ A S d W hY hP hA hW.2.1 hPW
  have hunW := IsUnitSec.mono hun hPW
  obtain ⟨c1, c2, c3⟩ := GlobalTheory.T.unit_section_divisor_eq K ι W f' g' hunW
  have hvert := GlobalTheory.T.vertical_statement_holds K ι I hI W n L C f' g' hW hL hC
    ⟨df', dg', hf', hg', hfW, hgW, fun k => by rw [hdeg k, hCa k, hBa k]⟩
    (fun W' _ => by rw [c1]) (fun W' _ hm => c2 W' hm) (fun z hz => by
      have hzP : z ∈ mcPts (mCoordIdeal y) := ⟨hz.1, fun f hf => hz.2 f (hPW hf)⟩
      obtain ⟨σ, hσ, -⟩ := GlobalTheory.T.complex_point_existsUnique_embedding K ι Ω F y φ hY z hzP
      have hz1 : u z = Real.log (S.κ σ) := (hu.near σ z hσ).self_of_nhds
      have hn := hnorm σ z hσ
      have hCz : C.h z = (S.κ σ * A.h z) ^ S.M := by
        rw [hCh, hBh, hz1, Real.exp_log (S.κ_pos σ), mul_comm]
      rw [hCz, mul_comm]
      exact hn)
  have hzero : I W (n + 1) (Fin.snoc L B) = 0 := by
    have h0 : (S.M : ℝ) * I W (n + 1) (Fin.snoc L B) = 0 := by
      rw [← hCI, hvert, c3 n L, sub_self]
    have hM : (S.M : ℝ) ≠ 0 := by exact_mod_cast S.M_pos.ne'
    exact (mul_eq_zero.mp h0).resolve_left hM
  rw [hchange, hzero, zero_sub]

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.JetAugmentationOnePthPower
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Coc.QAlg

theorem exists_const_add_dQ_mul (B : Type) [CommRing B] (m : ℕ) (x : Jet B Unit m) :
    ∃ (b : B) (y : Jet B Unit m), x = algebraMap B _ b + dQ B m * y := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective (I := orig B Unit ^ (m + 1)) x
  have hmem := sub_const_mem_orig P
  have hr : Set.range (MvPolynomial.X : Unit → MvPolynomial Unit B) = {MvPolynomial.X ()} :=
    Set.range_unique
  rw [orig, hr, Ideal.mem_span_singleton'] at hmem
  obtain ⟨Q, hQ⟩ := hmem
  refine ⟨MvPolynomial.constantCoeff P, Ideal.Quotient.mk _ Q, ?_⟩
  have hP : P = MvPolynomial.C (MvPolynomial.constantCoeff P) + Q * MvPolynomial.X () := by
    rw [hQ]; ring
  conv_lhs => rw [hP]
  rw [map_add, map_mul, mul_comm]
  rfl

theorem jetAug_dQ (B : Type) [CommRing B] (m : ℕ) :
    (jetAug : Jet B Unit m →ₐ[B] B) (dQ B m) = 0 := by
  show (jetAug : Jet B Unit m →ₐ[B] B)
    (Ideal.Quotient.mk (orig B Unit ^ (m + 1)) (MvPolynomial.X ())) = 0
  simp [jetAug, liftJet, Ideal.Quotient.liftₐ_apply]

theorem add_pow_of_natCast_eq_zero {A : Type} [CommRing A] (p : ℕ) (hp : p.Prime)
    (h : (p : A) = 0) (x y : A) : (x + y) ^ p = x ^ p + y ^ p := by
  rw [add_pow_prime_eq hp, h]
  simp

theorem pow_eq_one_add (B : Type) [CommRing B] (p : ℕ) [hp : Fact p.Prime] (h0 : (p : B) = 0)
    (e : Jet B Unit p) (he : (jetAug : Jet B Unit p →ₐ[B] B) e = 1) :
    ∃ v : B, e ^ p = 1 + dQ B p ^ p * algebraMap B _ (v ^ p) := by
  have hpJ : ((p : ℕ) : Jet B Unit p) = 0 := by
    rw [← map_natCast (algebraMap B (Jet B Unit p)) p, h0, map_zero]
  obtain ⟨b, y, rfl⟩ := exists_const_add_dQ_mul B p e
  have hb : b = 1 := by
    simpa only [map_add, map_mul, jetAug_dQ, zero_mul, add_zero, AlgHom.commutes,
      Algebra.algebraMap_self, RingHom.id_apply] using he
  subst hb
  obtain ⟨c, z, rfl⟩ := exists_const_add_dQ_mul B p y
  refine ⟨c, ?_⟩
  have h2 : dQ B p ^ p * dQ B p ^ p = 0 := by
    rw [← pow_add]
    exact pow_eq_zero_of_le (by have := hp.out.one_lt; omega) (dQ_pow B p)
  rw [map_one, add_pow_of_natCast_eq_zero p hp.out hpJ, one_pow, mul_pow,
    add_pow_of_natCast_eq_zero p hp.out hpJ, mul_pow, map_pow]
  linear_combination (z ^ p) * h2

end GlobalTheory.CompanionTheory.Ar.Coc.QAlg
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.JetLeftMem
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc.Pf

theorem gs_appLE {X Y : Scheme.{0}} (f : Y ⟶ X) (U : X.Opens) (V : Y.Opens) (e : V ≤ f ⁻¹ᵁ U) (y : Y) (hy : y ∈ V)
    (a : Γ(X, U)) : gs (𝟙 Y) y V ((f.appLE U V e).hom a) = gs f y U a := by
  have hf : f y ∈ U := e hy
  have key := Y.presheaf.germ_res_apply (homOfLE e) y hy ((f.app U).hom a)
  unfold gs
  rw [dif_pos hf]
  split_ifs with h1
  · exact key
  · exact absurd hy h1

theorem gm_spMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (u : Aˣ) (z : Sp B) :
    gm (spMap f) z ⊤ (unitΓ u) = gm (𝟙 _) z ⊤ (unitΓ (Units.map (f : A →* B) u)) := by
  have key := congrArg (fun g => (CommRingCat.Hom.hom g) (u : A)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at key
  unfold gm
  rw [dif_pos (show (spMap f) z ∈ (⊤ : (Sp A).Opens) from trivial)]
  rw [dif_pos (show (𝟙 (Sp B)) z ∈ (⊤ : (Sp B).Opens) from trivial)]
  apply Units.ext
  simp only [MonoidHom.comp_apply, Units.coe_map, pullU, unitΓ, toΓ, MonoidHom.coe_coe, Scheme.Hom.id_app, CommRingCat.hom_id, RingHom.id_apply]
  erw [key]
  rfl

theorem val_scale {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
    {Y Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ) (u : Γ(Y, ⊤)ˣ)
    (c : LB.Gen (LB.LinComb t.PP.L φ ε)) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ t.G.left) → t.PP.L.ι} (hJ : Good t.PP.L z J) :
    val (scaleGenG t φ ε u c) r z J = gm r z ⊤ u * val c r z J := by
  have hz : r z ∈ t.PP.L.wchart φ (fun k => J (r ≫ φ k)) := by
    show r z ∈ ⋂ k, ⇑(φ k) ⁻¹' ↑(t.PP.L.U (J (r ≫ φ k)))
    refine Set.mem_iInter.2 fun k => ?_
    have := hJ (r ≫ φ k)
    simpa [Scheme.Hom.comp_apply] using this
  unfold val scaleGenG
  erw [map_mul, gm_res r z _ hz]

theorem val_genPow {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
    {Y Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ)
    (c : LB.Gen (LB.LinComb t.PP.L φ ε)) (n : ℕ) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ t.G.left) → t.PP.L.ι) :
    val (genPowG t φ ε c n) r z J = val c r z J ^ n :=
  map_pow _ _ _

theorem jet_left_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
    {k : Type} [Field k] (x : Sp k ⟶ X0) {κ : Type} {n : ℕ} (j₀ : t.PP.L.ι)
    (hj₀ : ⊤ ≤ (1 : overAt x k ⟶ t.G).left ⁻¹ᵁ t.PP.L.U j₀) (ψ : overAt x (Jet k κ n) ⟶ t.G)
    (h : homAt x (jetAug : Jet k κ n →ₐ[k] k) ≫ ψ = 1) (q : Sp (Jet k κ n)) : ψ.left q ∈ t.PP.L.U j₀ := by
  have hsurj : Function.Surjective (jetAug : Jet k κ n →ₐ[k] k).toRingHom :=
    fun c => ⟨algebraMap k _ c, (jetAug : Jet k κ n →ₐ[k] k).commutes c⟩
  have hnil : ∀ a : Jet k κ n, jetAug a = 0 → IsNilpotent a := by
    intro a ha
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective a
    have h0 : MvPolynomial.constantCoeff P = 0 := by
      have : jetAug (Ideal.Quotient.mk _ P : Jet k κ n) = MvPolynomial.aeval (fun _ : κ => (0 : k)) P := rfl
      rw [this] at ha
      simpa [MvPolynomial.aeval_zero'] using ha
    have hP : P ∈ orig k κ := by
      have : P ∈ Ideal.span (MvPolynomial.X '' (Set.univ : Set κ)) := by
        rw [MvPolynomial.mem_ideal_span_X_image]
        intro m hm
        by_contra hc
        push_neg at hc
        have hm0 : m = 0 := by ext i; exact hc i (Set.mem_univ i)
        subst hm0
        rw [MvPolynomial.mem_support_iff, ← MvPolynomial.constantCoeff_eq] at hm
        exact hm h0
      simpa [orig, Set.image_univ] using this
    refine ⟨n + 1, ?_⟩
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow hP _
  have hrange := range_comap_of_surjective _ _ hsurj
  have huniv : PrimeSpectrum.zeroLocus (RingHom.ker (jetAug : Jet k κ n →ₐ[k] k).toRingHom : Set (Jet k κ n)) = Set.univ := by
    rw [PrimeSpectrum.zeroLocus_eq_univ_iff]
    intro a ha
    exact mem_nilradical.2 (hnil a (RingHom.mem_ker.1 ha))
  obtain ⟨p, hp⟩ : q ∈ Set.range (PrimeSpectrum.comap (jetAug : Jet k κ n →ₐ[k] k).toRingHom) := by
    rw [hrange, huniv]; trivial
  have hl := congrArg (fun g => Over.Hom.left g) h
  simp only [Over.comp_left] at hl
  have hq : ψ.left q = (1 : overAt x k ⟶ t.G).left p := by
    rw [← hl, ← hp]
    rfl
  rw [hq]
  exact hj₀ (show p ∈ (⊤ : (Sp k).Opens) from trivial)

end GlobalTheory.CompanionTheory.Ar.Coc.Pf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinModelPointsProjectStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.join_model_points_project : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M R : RootModel Ψ N) (i : R.Ω →+* M.Ω), IsArithVar (mCoordIdeal (joinOf M R i)) (dimFl Ψ N + 1) ∧ Birational (joinOf M R i) ∧ (∀ (L : Type) [Field L], ∀ z ∈ ptsOver L (mCoordIdeal (joinOf M R i)), (fun p => z (joinInl M.ι R.ι p)) ∈ ptsOver L M.P ∧ (fun p => z (joinInr M.ι R.ι p)) ∈ ptsOver L R.P) ∧ ∀ (L : Type) [Field L] [IsAlgClosed L], ∀ w ∈ ptsOver L M.P, ∃ z ∈ ptsOver L (mCoordIdeal (joinOf M R i)), (fun p => z (joinInl M.ι R.ι p)) = w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Ht.JoinFacts.main | exact GlobalTheory.CompanionTheory.Ar.Ht.JoinFacts.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Ht.JoinFacts.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineHeightInvariantScaling
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

namespace GlobalTheory.CompanionTheory.Ar.Ht

theorem lineHt_map_scale : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (A : HermLine ι) (L : Type) [Field L] [NumberField L] (L' : Type) [Field L'] [NumberField L'] (e : L →+* L') (w : (Σ k, ι k) → L) (c : K → L'), (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) → (∀ k, c k ≠ 0) → lineHt A L' (fun p => c p.1 * e (w p)) = lineHt A L w :=
  @CoverDenseAlt.lineHt_invariant_base_change_scaling

end GlobalTheory.CompanionTheory.Ar.Ht
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SubstitutionBilinearFormTransformStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.substitution_bilinear_form_transform : ∀ (R : Type) [CommRing R] (d d' : ℕ) (Qs : Fin d' → PS R 1 d) (f : PS R 2 d'), (∀ i, MvPowerSeries.constantCoeff (Qs i) = 0) → AxOne f → AxOne (subQ Qs f) ∧ bil (subQ Qs f) 1 1 = (linQ Qs).transpose * bil f 1 1 * linQ Qs := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.BilQ.bil_axOne_subQ | exact GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.BilQ.bil_axOne_subQ | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.BilQ.bil_axOne_subQ <;> assumption)
end


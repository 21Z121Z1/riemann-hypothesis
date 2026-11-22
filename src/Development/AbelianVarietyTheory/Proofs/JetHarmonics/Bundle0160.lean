import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0093
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0037
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsRadialPartPolyDiffOperatorClosed
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0115
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0207
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0159
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0038
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0033
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0027
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GramSpace
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0039
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroSplitOfLocalAndSum
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0011
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UwEllipticFlow
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0095
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0016
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0123
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0034
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0137
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0103
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0147
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0156
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
import Formalism.HermitianCurvature.Bundle0004
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0112
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointLeibnizExpansion

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsometryOfSabMap
section
noncomputable section

namespace GlobalTheory.LevelCusp

section Match

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Dict
open scoped Matrix ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

structure IsMatch (X X' : Data E r) (a : GL (Fin r) E) : Prop where
  psi : X.Ψ = X'.Ψ
  p0 : X.p0 = X'.p0
  xi : X.ξ0 = X'.ξ0
  iso : ∀ u v, herm X'.Gm ((a : Matrix (Fin r) (Fin r) E) *ᵥ u) ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) = herm X.Gm u v
  lat : ∀ v, v ∈ X.Λ ↔ (a : Matrix (Fin r) (Fin r) E) *ᵥ v ∈ X'.Λ

theorem isMatch_of_isUStab (X : Data E r) {a : GL (Fin r) E} (h : IsUStab X.Gm X.Λ a) : IsMatch X X a :=
  ⟨rfl, rfl, rfl, h.1, h.2⟩

theorem hermC_of_herm {G G' a : Matrix (Fin r) (Fin r) E} {ε : E}
    (h : ∀ u v, herm G' (a *ᵥ u) (a *ᵥ v) = ε * herm G u v) (τ : E →+* ℂ) (u v : Fin r → ℂ) :
    hermC τ G' (a.map τ *ᵥ u) (a.map τ *ᵥ v) = τ ε * hermC τ G u v := by
  classical
  have key : ∀ i j, ∑ p, ∑ q, τ (a p i) * τ (G' p q) * conj (τ (a q j)) = τ ε * τ (G i j) := fun i j => by
    have := congrArg τ (h (Pi.single i 1) (Pi.single j 1))
    simp only [herm, cc, Matrix.mulVec_single_one, Matrix.col_apply, map_sum, map_mul,
      IsCMField.complexEmbedding_complexConj] at this
    rw [this]
    simp [Pi.single_apply, apply_ite, ite_mul]
  have e : hermC τ G' (a.map τ *ᵥ u) (a.map τ *ᵥ v) =
      ∑ j, ∑ i, u i * (∑ p, ∑ q, τ (a p i) * τ (G' p q) * conj (τ (a q j))) * conj (v j) := by
    simp only [hermC, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun p _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_congr rfl fun p _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
  rw [e, Finset.sum_comm]
  simp only [key, hermC, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

variable {X X' : Data E r} {a : GL (Fin r) E}

theorem IsMatch.mem (h : IsMatch X X' a) (τ : X'.Ψ) : τ.1 ∈ X.Ψ := by rw [h.psi]; exact τ.2

theorem IsMatch.hermC_eq (h : IsMatch X X' a) (τ : E →+* ℂ) (u v : Fin r → ℂ) :
    hermC τ X'.Gm ((a : Matrix (Fin r) (Fin r) E).map τ *ᵥ u) ((a : Matrix (Fin r) (Fin r) E).map τ *ᵥ v) =
      hermC τ X.Gm u v := by
  rw [hermC_of_herm (ε := 1) (fun u v => by rw [h.iso, one_mul]), map_one, one_mul]

theorem IsMatch.dmin_eq (h : IsMatch X X' a) (x : Frame X.Ψ r) (τ : X'.Ψ) (i : Fin (r + 1)) :
    dmin X'.Gm (lact a (castFr h.psi x)) τ i = dmin X.Gm x ⟨τ.1, h.mem τ⟩ i := by
  unfold dmin
  congr 1
  ext p q
  exact h.hermC_eq τ.1 (col (mat x ⟨τ.1, h.mem τ⟩) p) (col (mat x ⟨τ.1, h.mem τ⟩) q)

theorem IsMatch.mem_dom (h : IsMatch X X' a) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    lact a (castFr h.psi x) ∈ X'.dom := fun τ => by
  refine ⟨?_, fun i => by rw [h.dmin_eq, ← h.p0]; exact (hx _).2 i⟩
  have e : mat (lact a (castFr h.psi x)) τ =
      (a : Matrix (Fin r) (Fin r) E).map τ.1 * mat x ⟨τ.1, h.mem τ⟩ := rfl
  rw [e, Matrix.det_mul]
  refine mul_ne_zero ?_ (hx _).1
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, map_ne_zero]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 a.isUnit).ne_zero

end Match

section Exp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UnifPoint GlobalTheory.LevStab
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {g : ℕ}
  {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {ty : Fin g → (E →+* ℂ)}

theorem exists_isometry_of_sabMap (F : FamilyUnif Xo σ ty) {ρ : Xo.X ⟶ Xo.X} (ν : SABMap Xo.univ.t Xo.univ.t ρ)
    {i j : Fin F.n} {P : (F.Di i).La →+ (Fin g → ℂ)} {P' : (F.Di j).La →+ (Fin g → ℂ)}
    (hP : IsPeriod (F.Di i) ty P) (hP' : IsPeriod (F.Di j) ty P') (hu : F.u i P ≫ ρ = F.u j P') :
    ∃ (gam : (F.Di i).La ≃ₗ[𝓞 E] (F.Di j).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
      (∀ a b, (F.Di j).EF (gam a) (gam b) = (F.Di i).EF a b) ∧ (∀ a, P' (gam a) = h (P a)) ∧
      ∀ z, (F.ex j P' (h z)).left = (F.ex i P z).left ≫ ν.φ := by
  obtain ⟨β, hβ⟩ := GlobalTheory.CMSpreadCompare.exists_pointEquiv ν.cart (Over.mk (F.u i P)) (s := F.u j P') hu.symm
  have hr : ReadsPeriods Xo.univ.t unitOn (F.Di i) ty P (fun z => β (F.ex i P z)) := by
    refine ⟨fun z => by rw [β.map_eq_one_iff, F.ex_ker i P hP], fun a z => ?_, fun k a b c hk hc => ?_⟩
    · apply Over.OverMorphism.ext
      rw [hβ, F.ex_lin i P hP, Over.comp_left, Over.comp_left, hβ, Category.assoc, Category.assoc]
      exact congrArg _ (ν.act a)
    · obtain ⟨w, hw, -⟩ := ν.lin
      have h₁ := (weilIs_grpPullback_of_comm _ _ Xo.univ.t.G Xo.univ.t.G ρ ν.φ _ _ Xo.univ.t.PP.isLB
        Xo.univ.t.PP.isLB ν.cart ⟨w, hw⟩ _ k _ _ (pushPt ν.cart.1.w _) (pushPt ν.cart.1.w _) _ rfl rfl).1
        (F.ex_weil i P hP k a b c hk hc)
      exact weilIs_congr hu (hβ _).symm (hβ _).symm h₁
  obtain ⟨gam, h, hEF, hh, hx⟩ := exists_isometry_of_hol hP hP' (e := fun z => β (F.ex i P z)) (e' := F.ex j P')
    (fun z w => by rw [F.ex_add i P hP, map_mul]) (β.surjective.comp (F.ex_onto i P hP))
    (by
      simp only [hβ]
      exact GlobalTheory.CMSpreadCompare.isHolTo_postcomp (GlobalTheory.ClassUniq.isHolTo_ex F i P hP) _)
    ⟨F.ex_add j P' hP', F.ex_onto j P' hP', GlobalTheory.ClassUniq.isHolTo_ex F j P' hP', (F.ex_diff j P' hP').1,
      (F.ex_diff j P' hP').2⟩ hr ⟨F.ex_ker j P' hP', F.ex_lin j P' hP', F.ex_weil j P' hP'⟩
  exact ⟨gam, h, hEF, hh, fun z => by rw [hx, hβ]⟩

end Exp

end GlobalTheory.LevelCusp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsRadialPartPolyDiffOperatorClosedStatement
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polyLift_one_mono_mul : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq), PolyLift P Bs 0 0 1 ∧ (∀ o o' κ κ' a, o ≤ o' → κ ≤ κ' → PolyLift P Bs o κ a → PolyLift P Bs o' κ' a) ∧ ∀ o₁ κ₁ o₂ κ₂ a b, PolyLift P Bs o₁ κ₁ a → PolyLift P Bs o₂ κ₂ b → PolyLift P Bs (o₁ + o₂) (κ₁ + κ₂) (a * b) := by
  first | exact @GlobalTheory.HatNF.polyLift_closed | exact GlobalTheory.HatNF.polyLift_closed | (intros; apply GlobalTheory.HatNF.polyLift_closed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MarkedLatticeIsometryDoubleCosetMove
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct
open GlobalTheory.ShortMove

namespace GlobalTheory.ShortMoveIso

open scoped Matrix

theorem transport {G A : Type} [Group G] [CommRing A] {n : ℕ} (f : G →* GL (Fin n) A)
    (Lh : G → AddSubgroup (Fin n → A)) (hL : ∀ g z, z ∈ Lh g ↔ ∃ y ∈ Lh 1, (f g).1 *ᵥ y = z) (N : ℕ) (δ u k : G)
    (hk : Lh k = Lh 1) :
    (∀ z, z ∈ Lh u ↔ (f δ).1 *ᵥ z ∈ Lh (δ * u * k)) ∧
      ∀ x x' a b, (∃ w ∈ Lh 1, (f k).1 *ᵥ a = b + N • w) → (∃ w ∈ Lh u, x - (f u).1 *ᵥ b = N • w) →
        (∃ w ∈ Lh (δ * u * k), x' - (f (δ * u * k)).1 *ᵥ a = N • w) →
        ∃ w ∈ Lh (δ * u * k), (f δ).1 *ᵥ x - x' = N • w := by
  have hmul : ∀ (a b : G) z, (f (a * b)).1 *ᵥ z = (f a).1 *ᵥ ((f b).1 *ᵥ z) := by
    intro a b z
    rw [map_mul, Units.val_mul, Matrix.mulVec_mulVec]
  have hone : ∀ z, (f 1).1 *ᵥ z = z := by
    intro z
    rw [map_one, Units.val_one, Matrix.one_mulVec]
  have h1 : ∀ z, z ∈ Lh u ↔ (f δ).1 *ᵥ z ∈ Lh (δ * u * k) := by
    intro z
    rw [hL u, hL (δ * u * k)]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨w, hw, rfl⟩ := (hL k y).1 (hk ▸ hy)
      exact ⟨w, hw, by rw [hmul, hmul]⟩
    · rintro ⟨y, hy, h⟩
      refine ⟨(f k).1 *ᵥ y, hk ▸ (hL k _).2 ⟨y, hy, rfl⟩, ?_⟩
      have := congrArg (fun v => (f δ⁻¹).1 *ᵥ v) h
      simp only [← hmul, inv_mul_cancel, hone] at this
      rw [← this, ← hmul, mul_assoc, inv_mul_cancel_left]
  refine ⟨h1, ?_⟩
  rintro x x' a b ⟨y, hy, ey⟩ ⟨w, hw, e⟩ ⟨w', hw', e'⟩
  refine ⟨(f δ).1 *ᵥ w - (f δ).1 *ᵥ ((f u).1 *ᵥ y) - w',
    sub_mem (sub_mem ((h1 w).1 hw) ((h1 _).1 ((hL u _).2 ⟨y, hy, rfl⟩))) hw', ?_⟩
  rw [sub_eq_iff_eq_add.1 e, sub_eq_iff_eq_add.1 e', hmul, hmul, ey]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, smul_sub]
  abel

theorem map_mem_half {R A : Type} [CommRing R] [AddCommGroup A] [Module R A] (I : Ideal R) (s : A →ₗ[R] A) :
    ∀ a ∈ I • (⊤ : Submodule R A), s a ∈ I • (⊤ : Submodule R A) := by
  intro a ha
  refine Submodule.smul_induction_on ha (fun m hm b _ => ?_) (fun x y hx hy => ?_)
  · rw [map_smul]
    exact Submodule.smul_mem_smul hm trivial
  · rw [map_add]
    exact add_mem hx hy

set_option maxHeartbeats 1000000 in

theorem marked_isometry : ∀ (D : D7) (V : HSp D) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (r : ℕ) (hr : V.rank = r) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (X X' : Data D.host.E r) (A A' : Datum H) (φ : A.La ≃ₗ[𝓞 D.host.E] X.Λ) (φ' : A'.La ≃ₗ[𝓞 D.host.E] X'.Λ) (t : Dw.La →ₗ[𝓞 D.host.E] A.La) (t' : Dw.La →ₗ[𝓞 D.host.E] A'.La) (s : Dw.La →ₗ[𝓞 D.host.E] Dw.La) (h γ κ : GA D V), ModelW V hr X → ModelW V hr X' → (∀ a b, ((A.EF a b : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-X.ξ0 * herm X.Gm (φ a : Fin r → D.host.E) (φ b))) → (∀ a b, ((A'.EF a b : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-X'.ξ0 * herm X'.Gm (φ' a : Fin r → D.host.E) (φ' b))) → γ ∈ GQ V → latGHat V κ = latGHat V 1 → (∀ a, ∃ w ∈ latGHat V 1, (finHom V κ).1.mulVec (finVec V (io a)) = finVec V (io (s a)) + l.M • w) → Marked V hr io l X.Λ (fun a => (φ (t a) : Fin r → D.host.E)) h → Marked V hr io l X'.Λ (fun a => (φ' (t' a) : Fin r → D.host.E)) (γ * h * κ) → ∃ gam : A.La ≃ₗ[𝓞 D.host.E] A'.La, (∀ a b, A'.EF (gam a) (gam b) = A.EF a b) ∧ ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ x, gam (t (s a)) = t' a + l.M • x := by
  intro D V H Dw l r hr io X X' A A' φ φ' t t' s h γ κ hW hW' hE hE' hγ hκ hs hm hm'
  subst hr
  obtain ⟨hΛ, hm⟩ := hm
  obtain ⟨hΛ', hm'⟩ := hm'
  obtain ⟨δ, hδu, hδf, -⟩ := GlobalTheory.MarkCoset.rational_matrix V γ hγ
  obtain ⟨ht1, ht2⟩ := transport (finHom V) (latGHat V) (fun g => (GlobalTheory.MarkCoset.latG_spec D V g).2) l.M γ h κ hκ
  have hmem : ∀ v, v ∈ X.Λ ↔ finVec V v ∈ latGHat V h := fun v => by
    rw [← (GlobalTheory.MarkCoset.latG_spec D V h).1, ← SetLike.mem_coe, hΛ]
    exact Set.ext_iff.1 (Set.image_id _) v
  have hmem' : ∀ v, v ∈ X'.Λ ↔ finVec V v ∈ latGHat V (γ * h * κ) := fun v => by
    rw [← (GlobalTheory.MarkCoset.latG_spec D V _).1, ← SetLike.mem_coe, hΛ']
    exact Set.ext_iff.1 (Set.image_id _) v
  have hlat : ∀ v, v ∈ X.Λ ↔ δ.1 *ᵥ v ∈ X'.Λ := fun v => by
    rw [hmem, hmem', ht1, hδf]
  have hM0 : l.M ≠ 0 := by have := l.three_le; omega
  have hri : ∀ v, δ.1 *ᵥ ((δ⁻¹).1 *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hli : ∀ v, (δ⁻¹).1 *ᵥ (δ.1 *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  let ψ : X.Λ ≃ₗ[𝓞 D.host.E] X'.Λ :=
    { toFun := fun v => ⟨δ.1 *ᵥ v.1, (hlat _).1 v.2⟩
      invFun := fun v => ⟨(δ⁻¹).1 *ᵥ v.1, (hlat _).2 (by rw [hri]; exact v.2)⟩
      map_add' := fun u v => Subtype.ext (Matrix.mulVec_add δ.1 u.1 v.1)
      map_smul' := fun a v => Subtype.ext (Matrix.mulVec_smul δ.1 a v.1)
      left_inv := fun v => Subtype.ext (hli _)
      right_inv := fun v => Subtype.ext (hri _) }
  let gam : A.La ≃ₗ[𝓞 D.host.E] A'.La := φ.trans (ψ.trans φ'.symm)
  have hgam : ∀ a, (φ' (gam a) : Fin V.rank → D.host.E) = δ.1 *ᵥ (φ a : Fin V.rank → D.host.E) := by
    intro a
    simp [gam, ψ]
  have hG : X.Gm = -V.gram.transpose := hW.1
  have hG' : X'.Gm = -V.gram.transpose := hW'.1
  have hξ : X'.ξ0 = X.ξ0 := hW'.2.trans hW.2.symm
  refine ⟨gam, fun a b => ?_, fun a ha => ?_⟩
  · have h1 := hE' (gam a) (gam b)
    rw [hgam, hgam, hG', hξ, hδu, ← hG, ← hE a b] at h1
    exact_mod_cast h1
  · obtain ⟨z, hz, e⟩ := ht2 (finVec V (φ (t (s a)) : Fin V.rank → D.host.E))
      (finVec V (φ' (t' a) : Fin V.rank → D.host.E)) _ _ (hs a) (hm _ (map_mem_half _ s a ha)) (hm' a ha)
    obtain ⟨w, hw, e'⟩ := GlobalTheory.MarkCoset.finVec_div V l.M hM0 (δ.1 *ᵥ (φ (t (s a)) : Fin V.rank → D.host.E) -
      (φ' (t' a) : Fin V.rank → D.host.E)) z (by
        rw [← e, hδf]
        funext i
        exact TensorProduct.tmul_sub _ _ _)
    refine ⟨φ'.symm ⟨w, (hmem' w).2 (hw ▸ hz)⟩, φ'.injective (Subtype.ext ?_)⟩
    rw [hgam, sub_eq_iff_eq_add'.1 e', map_add, map_nsmul, LinearEquiv.apply_symm_apply]
    rfl

end GlobalTheory.ShortMoveIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RadialPictureSmulCutoffGMultiplier
section
namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

noncomputable section

theorem jf_mulG {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (φ : ℝ → ℝ) (f : B.Mat k r → (Wq →L[ℂ] Wp))
    (g : B.Mat k r) : B.JF Bs (mulG Bs φ f) g = ((φ (Gf k r Bs.z Bs.z' g) : ℝ) : ℂ) • B.JF Bs f g := by
  show ∫ p, JF.xiP Bs p • B.rho Bs p (mulG Bs φ f) g ∂Bs.μSS =
    ((φ (Gf k r Bs.z Bs.z' g) : ℝ) : ℂ) • ∫ p, JF.xiP Bs p • B.rho Bs p f g ∂Bs.μSS
  rw [← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Bs] with p hp
  simp only [B.rho, mulG, Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp]
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_comm]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem cptCoef_mulG {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) {f : B.Mat k r → (Wq →L[ℂ] Wp)} (hf : KB.CptCoef Bs f) :
    KB.CptCoef Bs (mulG Bs φ f) := by
  obtain ⟨hs, ⟨R, hR⟩, ⟨δ, hδ, hG⟩⟩ := hf
  have hne : ∀ g, mulG Bs φ f g ≠ 0 → f g ≠ 0 := fun g h h0 => h (by simp [mulG, h0])
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun g : B.Mat k r => ((φ (Gf k r Bs.z Bs.z' g) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hφ.comp (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf Bs.z Bs.z'))
  exact ⟨Formalism.FourierDecayAlt.P.JCx2.pd_smooth_smul hc hs, ⟨R, fun g hg h => hR g hg (hne g h)⟩,
    ⟨δ, hδ, fun g hg h => hG g hg (hne g h)⟩⟩

theorem radial_mulG : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq), ∀ (φ : ℝ → ℝ) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), (ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → LE.SmoothLog φ ∧ (KB.CptCoef Bs f → KB.CptCoef Bs (mulG Bs φ f))) ∧ ∀ (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), IsMulG P Bs φ W → Top.IsRadOf P Bs Φ f → Top.IsRadOf P Bs (W 0 Φ) (mulG Bs φ f) := by
  intro Wp Wq _ _ _ _ _ _ P Bs φ f
  refine ⟨fun hφ => ⟨hφ.comp Real.contDiff_exp, fun hf => cptCoef_mulG Bs hφ hf⟩, ?_⟩
  intro W Φ hW hΦ x hx
  have hcell := Formalism.FourierDecayAlt.P.big_cell_values P.k P.r Wp Wq Bs x hx
  have hpos : 0 < gR P Bs x.1 x.2 := by
    have := hcell.1.2.1
    rw [hcell.2.2.2] at this
    exact this
  have hld : LE.ld 0 φ (gR P Bs x.1 x.2) = φ (gR P Bs x.1 x.2) := by
    simp only [LE.ld, iteratedDeriv_zero, Real.exp_log hpos]
  rw [hW 0 Φ x.1 x.2, hΦ x hx]
  simp only [Q.resG]
  rw [jf_mulG, hcell.2.2.2, hld, smul_comm]
  rfl

end

end GlobalTheory.HatNF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumLogPrimeDepthBoundsLeMulWeightSizeStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_log_prime_depth_bounds_le_mul_weight_size : ∀ (D : D7) (large₂ : SizeData₂ D) (j : ℕ) (w : WeightFamilies.Wt D j), 1 ≤ w.n → Real.log (WeightAlgebra.DF w) ≤ 2 * large₂.sc.L → (WeightAlgebra.DF w : ℝ) * (Real.log (WeightAlgebra.DF w) + 2.2) + (c2 D w * Real.log D.host.QS + cHalf w * Real.log D.host.q + cHalf w * Real.log D.host.d) + ∑ i : Fin 2, (WeightAlgebra.DF w : ℝ) / ((D.host.g i : ℝ) - 1) * Real.log (D.host.g i) ≤ WeightAlgebra.PN D large₂ * w.size := by
  first | exact @GlobalTheory.PtTie.depth_sum_le_PN | exact GlobalTheory.PtTie.depth_sum_le_PN | (intros; apply GlobalTheory.PtTie.depth_sum_le_PN <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaLawsUnitPeriod
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.GenusOne

variable {q : ℕ} [Fact q.Prime]

theorem norm_root_eq (M : Mdl q) (h : M.Ok) (δ : ℂ) (hδ : δ ^ 12 = M.L.g₂ ^ 3 - 27 * M.L.g₃ ^ 2) :
    ‖M.ι δ‖ = ‖M.ι M.c‖ ∧ ‖M.ι M.c‖ ≠ 0 := by
  obtain ⟨hc, -, -, -, -, -, hΔ, h4, h6⟩ := h
  have hιc : M.ι M.c ≠ 0 := (map_ne_zero M.ι).mpr hc
  refine ⟨?_, norm_ne_zero_iff.mpr hιc⟩

  rw [map_div₀, map_pow, eq_div_iff (pow_ne_zero 4 hιc)] at h4
  rw [map_div₀, map_pow, eq_div_iff (pow_ne_zero 6 hιc)] at h6
  have key : M.ι δ ^ 12 = M.ι M.c ^ 12 * M.W.Δ := by
    have e : M.ι δ ^ 12 = M.ι M.L.g₂ ^ 3 - 27 * M.ι M.L.g₃ ^ 2 := by
      rw [← map_pow, hδ]; simp only [map_sub, map_mul, map_pow, map_ofNat]
    rw [e, ← h4, ← h6]
    linear_combination (-(M.ι M.c ^ 12) / 1728) * M.W.c_relation
  have hn := congrArg norm key
  rw [norm_mul, norm_pow, norm_pow, hΔ, mul_one] at hn
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).mp hn

theorem norm_period (M : Mdl q) (ω : ℂ_[q]) (h : M.MChart ω) : ‖ω‖ * ‖M.ι M.c‖ = 1 := by
  obtain ⟨hok, h0, -, h1⟩ := h
  obtain ⟨-, -, -, -, -, -, hdu, -, hsmall⟩ := uw_elliptic_flow q M hok
  obtain ⟨han, -⟩ := hsmall 0 (Or.inl (zero_mem _))
  obtain ⟨-, -, -, hcc, hder, -, -⟩ := TaylorRead.hat_laws q M.ι (C ω * logS) h0

  have hd0 : ∀ f : ℂ_[q]⟦X⟧, constantCoeff (derivative ℂ_[q] f) = coeff 1 f := by
    intro f
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_derivative]
    simp
  have hℓ : coeff 1 (C ω * logS : ℂ_[q]⟦X⟧) = ω := by
    simp [logS, coeff_C_mul, coeff_mk]
  have e : coeff 1 (hat M.ι (C ω * logS) M.u) = ω * M.ι M.c := by
    rw [← hd0, hder M.u han, map_mul, hd0, hℓ, hcc, hdu]
  rw [e, norm_mul] at h1
  exact h1

theorem thetaLaws_unit_period : ∀ (d q : ℕ) [Fact q.Prime] (δ : ℂ), d.Prime → d % 16 = 7 → Split d q →
    δ ^ 12 = discr d → ∃ θ : ℂ → ℂ, IsTh d θ ∧ δ ≠ 0 ∧
      ∀ ι : ℂ ≃+* ℂ_[q], ∃ Ω : ℂ_[q], ‖Ω‖ = 1 ∧ ThetaLaws ι d (Ω / ι δ) θ := by
  intro d q _ δ hd h16 hsp hδ
  obtain ⟨⟨L, hL, hLd⟩, θ, hθ⟩ := GlobalTheory.T.exists_imagQuadOrder_pair_and_evenTheta d hd h16
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    exact (Basic.discr_eq hL).2 (by rw [← hδ]; norm_num)
  refine ⟨θ, hθ, hδ0, fun ι => ?_⟩
  obtain ⟨M, hMι, hML, hok, a1, a2, a3, a4, a6⟩ := GlobalTheory.T.exists_goodReduction_algebraic_weierstrass_model d q ι L hd h16 hL
  subst hMι
  have hL' : IsOK d M.L := by rw [hML]; exact hL
  obtain ⟨ω₀, hω₀⟩ := GlobalTheory.T.exists_multiplicativeChart_at_splitPrime d q M hd h16 hsp hL' hok a1 a2 a3 a4 a6
  obtain ⟨a, -, hω, hgood⟩ := GlobalTheory.T.exists_normalised_multiplicativeChart d q M ω₀ hd h16 hsp hL' hω₀
  have hδM : δ ^ 12 = M.L.g₂ ^ 3 - 27 * M.L.g₃ ^ 2 := by rw [hML, hLd]; exact hδ
  obtain ⟨hn, -⟩ := norm_root_eq M hok δ hδM
  have hp := norm_period M (ω₀ * zc a) hω
  have hιδ : M.ι δ ≠ 0 := (map_ne_zero M.ι).mpr hδ0
  refine ⟨ω₀ * zc a * M.ι δ, by rw [norm_mul, hn]; exact hp, ?_⟩
  rw [mul_div_cancel_right₀ _ hιδ]
  have hU0 : U1 d 0 θ = θ := (GlobalTheory.T.cmLattice_heisenberg_relations_one_variable d hd.pos).2.1 θ
  have h0 : PrimeTo d q 0 := ⟨1, one_pos, Nat.coprime_one_left q, 0, 0, by simp⟩
  have hB := GlobalTheory.T.cm_even_theta_series_chart_coeff_integral d q M (ω₀ * zc a) θ hd h16 hsp hL' hω hθ
  refine ⟨fun t ht => ?_, GlobalTheory.T.weilOperator_theta_translate_shift_prime_to_q d q M (ω₀ * zc a) θ hd h16 hsp hL' hω hθ hgood,
    GlobalTheory.T.norm_translate_powerComb_le_coprimeTranslation d q M (ω₀ * zc a) θ hd h16 hsp hL' hω hθ⟩

  have := GlobalTheory.T.norm_translate_powerComb_le_coprimeTranslation d q M (ω₀ * zc a) θ hd h16 hsp hL' hω hθ 1 1 (fun _ => 1) (fun _ => 0) t 1
    (fun _ => h0) ht (by simpa [hU0] using hB)
  simpa [hU0] using this

end GlobalTheory.MomOne.GenusOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TopVectorAddSmulCompactCoefficients
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory

namespace GlobalTheory.TopVec

open Filter Topology MeasureTheory in
private lemma opApply_smul {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wq] (Θ : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq) (c : ℂ)
    (F : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp) (g : _root_.Formalism.FourierDecayAlt.B.Mat k r) :
    _root_.Formalism.FourierDecayAlt.B.opApply Θ (c • F) g = c • _root_.Formalism.FourierDecayAlt.B.opApply Θ F g := by
  unfold _root_.Formalism.FourierDecayAlt.B.opApply
  simp only [_root_.Formalism.FourierDecayAlt.P.PositiveOrbitOpen.rw_smul, Pi.smul_apply, map_smul]
  rw [List.smul_sum, List.map_map]
  rfl

open Filter Topology MeasureTheory in
private lemma vecV_smul_jet_harmonics {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    (Bs : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (ν : Fin (2 * r + k + 1) → ℂ) (m : _root_.Formalism.FourierDecayAlt.B.Mat k r) (c : ℂ)
    (G : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp) (q : _root_.Formalism.FourierDecayAlt.C.LPt) :
    _root_.Formalism.FourierDecayAlt.D.vecV Bs ν m (fun g => c • G g) q = c • _root_.Formalism.FourierDecayAlt.D.vecV Bs ν m G q := by
  unfold _root_.Formalism.FourierDecayAlt.D.vecV
  split_ifs with h h'
  · apply _root_.Formalism.FourierDecayAlt.P.JCx1.needs.orbJ_smul_of_ae
    refine MeasureTheory.ae_of_all _ fun x => ?_
    unfold _root_.Formalism.FourierDecayAlt.D.orbIntegrand _root_.Formalism.FourierDecayAlt.B.rho
    simp only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
    exact smul_comm _ _ _
  · simp
  · simp

open Filter Topology MeasureTheory in
private lemma topLift_vecV_add_smul_lemma {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : _root_.Formalism.FourierDecayAlt.M.Par} (p : _root_.Formalism.FourierDecayAlt.KB.Pl P Wp Wq)
    {Cb : ℝ} (a : ℂ) {H₁ H₂ : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → (Wq →L[ℂ] Wp)} {w : List _root_.Formalism.FourierDecayAlt.C.Letter}
    (hdom : _root_.Formalism.FourierDecayAlt.KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hcut : _root_.Formalism.FourierDecayAlt.KB.CutWord P p.l0 w)
    (h₁ : _root_.Formalism.FourierDecayAlt.KB.CptCoef p.T.base H₁) (h₂ : _root_.Formalism.FourierDecayAlt.KB.CptCoef p.T.base H₂) (i : _root_.Formalism.FourierDecayAlt.Wd.Ix (Fin w.length))
    (q : _root_.Formalism.FourierDecayAlt.C.LPt) :
    p.V (p.Θ.Θ w i (H₁ + a • H₂)) q = p.V (p.Θ.Θ w i H₁) q + a • p.V (p.Θ.Θ w i H₂) q := by
  obtain ⟨nf, fib, o, κ, D, -, hD, -, -, hΘ⟩ := hdom w hcut i
  have hlen : ∀ T ∈ D, T.word.length ≤ o := fun T hT => by
    obtain ⟨_, _, _, _, es, -, -, hl, -⟩ := hD.2.2 T hT
    omega
  have hpos : ∀ g ∈ _root_.Formalism.FourierDecayAlt.B.GPos p.T.base, g ∈ _root_.Formalism.FourierDecayAlt.C6.domL p.T.base ∅ :=
    fun g hg => ⟨hg.1, hg.2, by simp⟩
  have hc₁ : _root_.Formalism.FourierDecayAlt.KB.CptCoef p.T.base (_root_.Formalism.FourierDecayAlt.B.opApply D H₁) := _root_.Formalism.FourierDecayAlt.P.TLB.cpt_op h₁ hD.1
  have hc₂ : _root_.Formalism.FourierDecayAlt.KB.CptCoef p.T.base (_root_.Formalism.FourierDecayAlt.B.opApply D H₂) := _root_.Formalism.FourierDecayAlt.P.TLB.cpt_op h₂ hD.1
  have e₁ : p.V (p.Θ.Θ w i H₁) q = p.V (_root_.Formalism.FourierDecayAlt.B.opApply D H₁) q :=
    _root_.Formalism.FourierDecayAlt.P.PBE.vecV_congrGPos _ _ _ _ fun g hg => hΘ H₁ g (hpos g hg)
  have e₂ : p.V (p.Θ.Θ w i H₂) q = p.V (_root_.Formalism.FourierDecayAlt.B.opApply D H₂) q :=
    _root_.Formalism.FourierDecayAlt.P.PBE.vecV_congrGPos _ _ _ _ fun g hg => hΘ H₂ g (hpos g hg)
  have e₃ : p.V (p.Θ.Θ w i (H₁ + a • H₂)) q =
      p.V (fun g => _root_.Formalism.FourierDecayAlt.B.opApply D H₁ g - (fun g => (-a) • _root_.Formalism.FourierDecayAlt.B.opApply D H₂ g) g) q := by
    refine _root_.Formalism.FourierDecayAlt.P.PBE.vecV_congrGPos _ _ _ _ fun g hg => ?_
    have hsum : H₁ + a • H₂ = H₁ - (-a) • H₂ := by rw [neg_smul, sub_neg_eq_add]
    rw [hΘ _ g (hpos g hg), hsum,
      _root_.Formalism.FourierDecayAlt.P.PBE.opApply_subGV D hlen (_root_.Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic.ckOn_top_nat h₁.1 o) (_root_.Formalism.FourierDecayAlt.P.B4.ckOn_smul (-a) (_root_.Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic.ckOn_top_nat h₂.1 o)) g hg.1, opApply_smul]
  have e₄ := _root_.Formalism.FourierDecayAlt.P.PBN.vecV_sub p.T.base p.ν' p.m₀ q hc₁ (_root_.Formalism.FourierDecayAlt.P.PBN.cpt_smul p.T.base (-a) hc₂)
  have e₅ := vecV_smul_jet_harmonics p.T.base p.ν' p.m₀ (-a) (_root_.Formalism.FourierDecayAlt.B.opApply D H₂) q
  rw [e₁, e₂, e₃]
  change _root_.Formalism.FourierDecayAlt.D.vecV _ _ _ _ q = _root_.Formalism.FourierDecayAlt.D.vecV _ _ _ _ q + a • _root_.Formalism.FourierDecayAlt.D.vecV _ _ _ _ q
  rw [e₄, e₅, neg_smul, sub_neg_eq_add]

open Filter Topology MeasureTheory in
private lemma hsVec_add_jet_harmonics {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (A B : Wq →L[ℂ] Wp) : _root_.Formalism.FourierDecayAlt.B.hsVec (A + B) = _root_.Formalism.FourierDecayAlt.B.hsVec A + _root_.Formalism.FourierDecayAlt.B.hsVec B := by
  unfold _root_.Formalism.FourierDecayAlt.B.hsVec
  rfl

open Filter Topology MeasureTheory in

theorem _root_.GlobalTheory.TopVec.tv_add_smul : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : _root_.Formalism.FourierDecayAlt.M.Par) (p : _root_.Formalism.FourierDecayAlt.KB.Pl P Wp Wq) (Cb : ℝ) (a : ℂ) (H₁ H₂ : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List _root_.Formalism.FourierDecayAlt.C.Letter) (c : Fin (P.r + 1) → ℂ), _root_.Formalism.FourierDecayAlt.KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → _root_.Formalism.FourierDecayAlt.KB.CutWord P p.l0 w → _root_.Formalism.FourierDecayAlt.KB.CptCoef p.T.base H₁ → _root_.Formalism.FourierDecayAlt.KB.CptCoef p.T.base H₂ → _root_.GlobalTheory.TopVec.tv p (H₁ + a • H₂) w c = _root_.GlobalTheory.TopVec.tv p H₁ w c + a • _root_.GlobalTheory.TopVec.tv p H₂ w c := by
  intro Wp Wq _ _ _ _ _ _ P p Cb a H₁ H₂ w c hdom hcut h₁ h₂
  unfold _root_.GlobalTheory.TopVec.tv
  rw [← WithLp.toLp_smul, ← WithLp.toLp_add]
  congr 1
  funext x
  rw [topLift_vecV_add_smul_lemma p a hdom hcut h₁ h₂, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.comp_smul, hsVec_add_jet_harmonics, _root_.Formalism.FourierDecayAlt.P.TBBx2.Tri.hsVec_smul, smul_add, Pi.add_apply, Pi.smul_apply,
    smul_comm a]

end GlobalTheory.TopVec
end


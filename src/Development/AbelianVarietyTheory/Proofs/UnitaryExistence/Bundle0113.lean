import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0112
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0026
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.Bundle0001
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0072
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0107
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSplitLatticeDatumEverySignature
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028
import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0025
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0040
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CuspFormsDominantWeightFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0092
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0096
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0071
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0068
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0073
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CuspL2AndDefinite

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CuspSectionAdelicLeftInvariantContinuousStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspSection_adelic_leftInvariant_continuous : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ dict, C.IsDict dict → ∀ mu : GA D V → ℂ, (∀ g g', mu (g * g') = mu g * mu g') → (∀ γ ∈ GQ V, mu γ = 1) → Continuous mu → ∀ (la : ∀ k, Wt (C.M.X k).Ψ r) (P : FDSec C.M.X), IsHolCusp C.M.X la P → (∀ γ ∈ GQ V, ∀ g, adel V dict mu P (γ * g) = adel V dict mu P g) ∧ Continuous (adel V dict mu P) := by
  first | exact @GlobalTheory.Member.adel_leftInv_and_continuous | exact GlobalTheory.Member.adel_leftInv_and_continuous | (intros; apply GlobalTheory.Member.adel_leftInv_and_continuous <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DictIsUnifOfMarkingRuleDictionaryStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dictIsUnif_of_markingRule_dictionary : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ dict, C.IsDict dict → ∀ Kf : Subgroup (GA D V), IsLevelK V l.M Kf → DictIsUnif V dict Kf C.th C.hr := by
  first | exact @GlobalTheory.Member.dictIsUnif_of_isDict | exact GlobalTheory.Member.dictIsUnif_of_isDict | (intros; apply GlobalTheory.Member.dictIsUnif_of_isDict <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFrameUniformisationPrescribedSpaceStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frameUniformisation_prescribedSpace : N1c → GlobalTheory.Published.HasseNormSt → Out.SecBaseChangeSt → Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (ξ₀ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : Dw.La →ₗ[𝓞 E] (Fin r → E)), 1 ≤ Dw.p + Dw.q → GoodEmb c σ → cc ξ₀ = -ξ₀ → (∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → (τ ξ₀).im < 0) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ₀ * herm Gm (φ x) (φ y))) → ∃ U : Unf Xo c σ r, IsUnf U ∧ Nonempty U.Comp ∧ (∀ k la γ, (U.X k).χ la γ = 1) ∧ (∀ k, (U.X k).Gm = Gm ∧ (U.X k).ξ0 = ξ₀) ∧ (∀ k x, FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (U.un k x)) ∧ ∀ ρ, FJ.LatZ U.X ρ ∧ (l.A = 1 → FJ.ExpoMatch U.X 1 ρ l.M) := by
  first | exact @GlobalTheory.FrameUnif.exists_unf_of_space | exact GlobalTheory.FrameUnif.exists_unf_of_space | (intros; apply GlobalTheory.FrameUnif.exists_unf_of_space <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsometryOfConjugateSplitPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isometry_of_conjugate_split_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∀ (C : Curve H) (io : C.P.A.left ⟶ C.P.A.left), IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) io → ∀ (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), ∀ (i' : Fin F.n) (P' : (F.Di i').La →+ (Fin g → ℂ)) (hP' : IsPeriod (F.Di i') ty P'), IsSplit hP → spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u i' P' → ∃ Φ : (F.Di i).La ≃ₗ[𝓞 E] (F.Di i').La, (∀ a b, (F.Di i').EF (Φ a) (Φ b) = (F.Di i).EF a b) ∧ (∀ a, Φ a ∈ lat hP' H.rt0 ↔ a ∈ lat hP H.rt0) ∧ (∀ a, Φ a ∈ lat hP' (-H.rt0) ↔ a ∈ lat hP (-H.rt0)) ∧ ∀ (n : ℕ) (s : ℤ × ℤ), 0 < n → C.ActsBy τ io n s → ∀ a ∈ lat hP H.rt0, ∀ b ∈ lat hP (-H.rt0), spMap (τ : ℂ →+* ℂ) ≫ (F.ex i P ((n : ℂ)⁻¹ • P (a + b))).left = (F.ex i' P' ((n : ℂ)⁻¹ • P' (Φ (wE H s • a + H.bar (wE H s) • b)))).left := by
  first | exact @GlobalTheory.CompRat.exists_isometry_of_conj_split | exact GlobalTheory.CompRat.exists_isometry_of_conj_split | (intros; apply GlobalTheory.CompRat.exists_isometry_of_conj_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeIsometryConjSplitPointAnyLevel
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat

open ConjIsometry in

theorem exists_isometry_of_conj_split_anyLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∀ (C : Curve H) (io : C.P.A.left ⟶ C.P.A.left), IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) io → ∀ (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), ∀ (i' : Fin F.n) (P' : (F.Di i').La →+ (Fin g → ℂ)) (hP' : IsPeriod (F.Di i') ty P'), IsSplit hP → spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u i' P' → ∃ Φ : (F.Di i).La ≃ₗ[𝓞 E] (F.Di i').La, (∀ a b, (F.Di i').EF (Φ a) (Φ b) = (F.Di i).EF a b) ∧ (∀ a, Φ a ∈ lat hP' H.rt0 ↔ a ∈ lat hP H.rt0) ∧ (∀ a, Φ a ∈ lat hP' (-H.rt0) ↔ a ∈ lat hP (-H.rt0)) ∧ ∀ (n : ℕ) (s : ℤ × ℤ), 0 < n → C.ActsBy τ io n s → ∀ a ∈ lat hP H.rt0, ∀ b ∈ lat hP (-H.rt0), spMap (τ : ℂ →+* ℂ) ≫ (F.ex i P ((n : ℂ)⁻¹ • P (a + b))).left = (F.ex i' P' ((n : ℂ)⁻¹ • P' (Φ (wE H s • a + H.bar (wE H s) • b)))).left := by
  intro E _ _ _ H D l Xo σ g ty F h1 hσ hty τ hτ C io hio i P hP i' P' hP' hs hu
  obtain ⟨Φ, hinj, hp, hm, hact⟩ :=
    GlobalTheory.T.exists_lattice_linearMap_conjugate_splitPoint E H D l Xo σ g ty F h1 hσ hty τ hτ C io hio i P hP i' P' hP' hs hu
  have hiso : ∀ x y, (F.Di i').EF (Φ x) (Φ y) = (F.Di i).EF x y := by
    intro x y
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hs.ge (Submodule.mem_top (x := x)))
    obtain ⟨a', ha', b', hb', rfl⟩ := Submodule.mem_sup.1 (hs.ge (Submodule.mem_top (x := y)))
    have key : ∀ n : ℕ, 0 < n →
        (n : ℤ) ∣ (F.Di i').EF (Φ (a + b)) (Φ (a' + b')) - (F.Di i).EF (a + b) (a' + b') := by
      intro n hn
      obtain ⟨⟨s, hs⟩, -⟩ := GlobalTheory.T.conjugation_acts_on_cm_torsion_by_multiplication E H C τ hτ io hio n hn
      have k := conj_pairing F τ hP hP' hu hn (hact n s hn hs a ha b hb) (hact n s hn hs a' ha' b' hb')
      have hN := GlobalTheory.T.cyclotomicCharacter_eq_cmMultiplier_norm E H C τ hτ io n s hn hs
      have hb1 := bar_mul_wE (H := H) s
      generalize s.1 ^ 2 + s.1 * s.2 + s.2 ^ 2 * (((H.d : ℤ) + 1) / 4) = N at hN hb1
      have hb2 : H.bar (H.bar (wE H s)) * H.bar (wE H s) = N := by rw [bar_bar, mul_comm, hb1]
      have o : ∀ u ∈ lat hP H.rt0, ∀ v ∈ lat hP (-H.rt0),
          (F.Di i').EF (Φ u) (Φ v) = 0 ∧ (F.Di i').EF (Φ v) (Φ u) = 0 := fun u hu v hv => by
        have := form_lat_eq_zero hP' ((hp u).2 hu) ((hm v).2 hv)
        exact ⟨this, by rw [form_skew, this, neg_zero]⟩
      have e : (F.Di i').EF (Φ (wE H s • a + H.bar (wE H s) • b)) (Φ (wE H s • a' + H.bar (wE H s) • b')) =
          N * (F.Di i').EF (Φ (a + b)) (Φ (a' + b')) := by
        simp only [map_add, LinearMap.add_apply]
        rw [(o _ (Submodule.smul_mem _ _ ha) _ (Submodule.smul_mem _ _ hb')).1,
          (o _ (Submodule.smul_mem _ _ ha') _ (Submodule.smul_mem _ _ hb)).2, (o _ ha _ hb').1, (o _ ha' _ hb).2]
        simp only [map_smul Φ]
        rw [form_smul_smul _ _ _ hb1, form_smul_smul _ _ _ hb2]
        ring
      rw [e, ← mul_neg, zpow_mul, ← hN] at k
      have prim : IsPrimitiveRoot (τ (zeta n)) n :=
        (Complex.isPrimitiveRoot_exp n hn.ne').map_of_injective τ.injective
      have ne : τ (zeta n) ≠ 0 := prim.ne_zero hn.ne'
      rw [← prim.zpow_eq_one_iff_dvd, sub_eq_add_neg, zpow_add₀ ne, k, ← zpow_add₀ ne, add_neg_cancel, zpow_zero]
    have := key (((F.Di i').EF (Φ (a + b)) (Φ (a' + b')) - (F.Di i).EF (a + b) (a' + b')).natAbs + 1) (by omega)
    exact sub_eq_zero.1 (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs this (by rw [Int.natAbs_natCast]; exact Nat.lt_succ_self _))
  have hsurj := surjective_of_isometry
    (by rw [(F.sig i).1, (F.sig i).2, (F.sig i').1, (F.sig i').2]) Φ hinj hiso
  exact ⟨LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩, hiso, hp, hm, hact⟩

end GlobalTheory.CompRat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSplitLatticeDatumEverySignatureStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitLattice_datum_every_signature : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (p q : ℕ), (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0) → ∃ D₀ : Datum H, D₀.p = p ∧ D₀.q = q ∧ SplitLat D₀ := by
  first | exact @GlobalTheory.CompRat.exists_splitLat_of_signature | exact GlobalTheory.CompRat.exists_splitLat_of_signature | (intros; apply GlobalTheory.CompRat.exists_splitLat_of_signature <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NormEmbeddingHostFormConstantEq
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.ExtCore

theorem norm_embedding_hostFormConstant_eq (D : D7) (τ : D.host.E →+* ℂ) : ‖τ D.host.xi0‖ = xiR D := by
  unfold xiR
  have hs : ∀ σ : D.host.E →+* ℂ, ‖σ D.host.sqrtMinusD‖ ^ 2 = ‖(D.host.d : ℂ)‖ := fun σ => by
    rw [← norm_pow, sq_emb, norm_neg]
  have hn : ‖τ D.host.sqrtMinusD‖ = ‖D.host.φ₀ D.host.sqrtMinusD‖ :=
    (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ((hs τ).trans (hs _).symm)
  rw [show D.host.xi0 = -1 / ((Ideal.absNorm D.host.ccK : D.host.E) * D.host.sqrtMinusD) from rfl]
  simp only [map_div₀, map_neg, map_one, map_mul, map_natCast, norm_div, norm_neg, norm_one, norm_mul, hn]

theorem isDetRoot_mul {D : D7} (V : HSp D) (g g' : GA D V) (x x' : (AE D)ˣ) (hx : IsDetRoot V g x)
    (hx' : IsDetRoot V g' x') : IsDetRoot V (g * g') (x * x') := by
  unfold IsDetRoot at *
  rw [Units.val_mul, (matHom V).map_mul, Units.val_mul, Matrix.det_mul, RingHom.map_mul]
  conv_lhs => rw [hx, hx']
  ring

theorem muVal_mul {D : D7} {V : HSp D} {χ : (AE D)ˣ →* Circle} {mu : GA D V → ℂ} (h : MuVal V χ mu)
    (g g' : GA D V) : mu (g * g') = mu g * mu g' := by
  obtain ⟨x, hx⟩ := h.1 g
  obtain ⟨x', hx'⟩ := h.1 g'
  rw [h.2 _ _ (isDetRoot_mul V g g' x x' hx hx'), h.2 _ _ hx, h.2 _ _ hx', map_mul, Circle.coe_mul]

theorem exists_latEmb (D : D7) (Q : Par D) (hQ : Q.Pins) (j : ℕ) :
    ∃ ι₀ : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E), ∀ hj : InR D j,
      let io := LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (D.sp.W_rank j hj.1 hj.2)) ∘ₗ ι₀
      LatEmb (D.sp.W j) io ∧ LatIsom (D.sp.W j) (Q.Dw j).EF io ∧
        ∀ x y, (((Q.Dw j).EF x y : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-(-D.host.xi0) *
          herm (gmW (D.sp.W j) (D.sp.W_rank j hj.1 hj.2)) (io x ∘ Fin.cast (D.sp.W_rank j hj.1 hj.2).symm)
            (io y ∘ Fin.cast (D.sp.W_rank j hj.1 hj.2).symm)) := by
  by_cases hj : InR D j
  · obtain ⟨io, h1, h2, -, -, -, h3⟩ := GlobalTheory.RecDict.exists_latEmb_sign_one D Q hQ j hj
    refine ⟨LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (D.sp.W_rank j hj.1 hj.2).symm) ∘ₗ io, fun hj' => ?_⟩
    have he : LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (D.sp.W_rank j hj'.1 hj'.2)) ∘ₗ
        (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (D.sp.W_rank j hj.1 hj.2).symm) ∘ₗ io) = io := by
      ext x i
      rfl
    intro io'
    have : io' = io := he
    rw [this]
    exact ⟨h1, h2, h3⟩
  · exact ⟨0, fun h => absurd h hj⟩

set_option maxHeartbeats 1000000 in

theorem exists_coreJ : PartI → N1ab → N1c → ThetaUnifAV → Out.Laws → Out.Laws2 → GlobalTheory.Published.HasseNormSt → ∀ (D : D7) (Q : Par D), Q.Pins → (∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q) → VolTieG D → ∀ (chiW : ℕ → (Q.c.F →+* ℂ) → (AE D)ˣ →* Circle) (mu : ∀ j, (Q.c.F →+* ℂ) → GA D (D.sp.W j) → ℂ), (∀ j, InR D j → ∀ σ, GoodEmb Q.c σ → MuVal (D.sp.W j) (chiW j σ) (mu j σ) ∧ (∀ γ ∈ GQ (D.sp.W j), mu j σ γ = 1) ∧ Continuous (mu j σ) ∧ MuConj Q.c.F.val.toRingHom σ (chiW j Q.c.F.val.toRingHom) (chiW j σ)) → ∃ T : CoreJ D, LawsJ T ∧ LawsCore T.toCore ∧ T.Q = Q ∧ HEq T.chiW chiW := by
  intro hI hA hC hTh hL hL2 hH D Q hQ hpq hV chiW mu hmu
  have hB := hL.secBaseChange
  have hT := hL2.secTwist
  have h0 : GoodEmb Q.c Q.c.F.val.toRingHom := rfl
  have h1 : InR D 1 := ⟨le_rfl, by have := D.R.two_le_m; omega⟩
  obtain ⟨hgood, -, -⟩ := GlobalTheory.RecDict.level_good_and_sign D Q hQ
  obtain ⟨pb, hpb⟩ := GlobalTheory.LevelHalf.half_eq_prod D Q hQ
  choose ι hι using exists_latEmb D Q hQ
  choose Kf hKf _hKf' using fun j => GlobalTheory.RecDict.exists_isLevelK D (D.sp.W j) (D.host.g 0 * D.host.g 1)
  have hpk := fun j (hj : InR D j) σ (hσ : GoodEmb Q.c σ) =>
    GlobalTheory.T.lattice_embedding_trace_form hI hA hC hTh hL hL2 hH D Q hQ hpq j hj σ hσ _ (hι j hj).1 (hι j hj).2.2 (Kf j) (hKf j)
  have hne : Nonempty (Data D.host.E D.R.r) := by
    obtain ⟨U, dict, -⟩ := hpk 1 h1 _ h0
    exact ⟨U.X (dict 1).1⟩
  have hall : ∀ j (σ : Q.c.F →+* ℂ), ∃ (U : Unf (Q.Xo j) Q.c σ D.R.r)
      (dict : GA D (D.sp.W j) → Σ k, Frame (U.X k).Ψ D.R.r)
      (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ), ∀ hj : InR D j, GoodEmb Q.c σ →
      ∃ th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ),
      IsUnf U ∧ (∀ k la γ, (U.X k).χ la γ = 1) ∧ (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictIsUnif (D.sp.W j) dict (Kf j) th (D.sp.W_rank j hj.1 hj.2) ∧ (∀ g τ i, ‖dmin (U.X (dict g).1).Gm (dict g).2 τ i‖ = 1) ∧ (∀ g₀ : GA D (D.sp.W j), ∃ N ∈ 𝓝 g₀, ∃ (k : _) (x : GA D (D.sp.W j) → Frame (U.X k).Ψ _), ContinuousOn x N ∧ ∀ g ∈ N, x g ∈ (U.X k).dom ∧ ∃ γ ∈ (U.X k).Γ, dict g = ⟨k, lact γ (x g)⟩) ∧ (∀ k, ModelW (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) (U.X k) ∧ IsOrthogonalFrame (U.X k) x₀) ∧ FJ.LatZ U.X (WeightFamilies.rho D j) ∧ FJ.CuNeF U.X (WeightFamilies.rho D j) ∧ FJ.ExpoMatch U.X 1 (WeightFamilies.rho D j) (D.host.g 0 * D.host.g 1) ∧ ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin ((Q.Dw j).mult τ)) (F : FamilyUnif (Q.Xo j) (σ.comp (IntermediateField.inclusion Q.c.le).toRingHom) (fun i => relab Q.c σ (e i).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ), DictLat U (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) dict (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (D.sp.W_rank j hj.1 hj.2)) ∘ₗ ι j) e F ik φ th x₀ := by
    intro j σ
    by_cases h : InR D j ∧ GoodEmb Q.c σ
    · obtain ⟨U, dict, x₀, h'⟩ := hpk j h.1 σ h.2
      exact ⟨U, dict, x₀, fun _ _ => h'⟩
    · obtain ⟨U, ⟨p⟩⟩ := GlobalTheory.exists_unf_nonempty_frame hC hT D Q hpq hne j σ
      exact ⟨U, fun _ => p, fun _ => 1, fun hj hσ => absurd ⟨hj, hσ⟩ h⟩
  choose U dict x₀ th hunf hchi hth hdict hunit hloc hmod hlatZ hcu hexpo hpin using hall
  have hmuU : ∀ j, InR D j → ∀ σ, GoodEmb Q.c σ → MuUnit (D.sp.W j) (dict j σ) (mu j σ) := fun j hj σ hσ =>
    ⟨muVal_mul (hmu j hj σ hσ).1, (hmu j hj σ hσ).1.norm, (hmu j hj σ hσ).2.1, hunit j σ hj hσ⟩
  have hsup : ∀ j, InR D j → SupDef (Q.Xo j) Q.c (U j) := fun j hj =>
    supDef_of _ _ _ fun a n _ σ hσ f hf hz =>
      (GlobalTheory.reading_linearIndependent_and_injective hB _ _ _ _ (Q.Xo j) Q.c σ _
        (Formalism.L2.PjFree.Unf.ofPj (U j σ)) ((Formalism.L2.PjFree.isUnf_ofPj _).2 (hunf j σ hj hσ)) a n).2 f
        ((mem_cusp _ _ _ _ _ _).1 hf).1 hz
  have hsq := fun j (hj : InR D j) σ (hσ : GoodEmb Q.c σ) =>
    GlobalTheory.CuspSqInt.cusp_l2_and_definite D _ _ _ (Q.Xo j) Q.c _ (U j) σ (D.sp.W j) (dict j σ) (mu j σ) (Kf j)
      (th j σ hj hσ) _ hV (D.sp.W_sig j) hσ (hchi j σ hj hσ) (hdict j σ hj hσ) (hmuU j hj σ hσ)
      (hmu j hj σ hσ).2.2.1 (hloc j σ hj hσ) (hsup j hj)
  have halg := fun j => GlobalTheory.Frames.algebraic_laws hB _ _ _ _ (Q.Xo j) Q.c
  let T : CoreJ D :=
    { Q := Q, U := U, V := fun j _ => D.sp.W j, dict := dict, mu := mu, Kf := fun j _ => Kf j, pb := pb,
      cE := fun _ _ _ => 1, chiW := chiW, x₀ := x₀, iota := ι }
  have hM : LawsM T.toCore :=
    { pins := hQ
      half := hpb
      evalWD := fun j _ => (halg j).2.2.1
      unf := fun j hj σ hσ => hunf j σ hj hσ
      unTest := fun j _ σ _ k x =>
        haveI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
        GlobalTheory.Frames.allTest_of_secBaseChange hB _ _ _ _ (Q.Xo j) Q.c (CAt σ) ((U j σ).un k x)
      chiTriv := fun j hj σ hσ _ _ _ k γ _ => hchi j σ hj hσ k _ γ
      dictU := fun j hj σ hσ => ⟨th j σ hj hσ, _, hth j σ hj hσ, hdict j σ hj hσ⟩
      spaceW := fun _ _ _ _ => rfl
      levelK := fun j _ _ _ => hKf j
      xiAbs := fun j hj σ hσ k τ =>
        (congrArg (fun z => ‖τ z‖) (hmod j σ hj hσ k).1.2).trans (by rw [map_neg, norm_neg]; exact norm_embedding_hostFormConstant_eq D τ)
      muUnit := hmuU
      muCont := fun j hj σ hσ => (hmu j hj σ hσ).2.2.1
      finVol := fun j _ _ _ => finVol_alt hV j
      cuspFD := fun j hj => (Formalism.L2.PjFree.cuspFD_ofPj (U j)).1
        (GlobalTheory.cuspForms_finiteDimensional_of_isUnf hB _ _ _ _ (Q.Xo j) Q.c _
          (fun σ => Formalism.L2.PjFree.Unf.ofPj (U j σ)) _ h0 ((Formalism.L2.PjFree.isUnf_ofPj _).2 (hunf j _ hj h0)))
      supDef := hsup
      cuspidalL2Subspace := fun j hj σ hσ => (hsq j hj σ hσ).choose
      l2Def := fun j hj σ hσ => (hsq j hj σ hσ).choose_spec
      unitIndep := fun j _ => (halg j).2.2.2.2.2.1
      ptNe := fun j _ =>
        GlobalTheory.integralAlgebraicFramedPoint_exists hI hA hC hB hT _ _ _ _ (Q.Xo j) Q.c (hpq j) hgood }
  refine ⟨T, ?_, ?_, rfl, HEq.rfl⟩
  · exact
      { toLawsM := hM
        cUnit := fun _ _ _ _ _ => norm_one
        muVal := fun j hj σ hσ => (hmu j hj σ hσ).1
        muConj := fun j hj σ hσ => (hmu j hj σ hσ).2.2.2
        intAll := fun j _ => GlobalTheory.IntegralFrames.intAll hI hA hB hT _ _ _ _ (Q.Xo j) Q.c (hpq j) hgood
        modelW := fun j hj σ hσ => ⟨_, fun k => (hmod j σ hj hσ k).1⟩
        familyUniformisationBasePointOrthogonal := fun j hj σ hσ k => (hmod j σ hj hσ k).2
        kfHalf := fun j _ _ _ => GlobalTheory.LevelHalf.kfHalf_record D Q hQ j (Kf j) (hKf j)
        adPin := fun j hj σ hσ => by
          obtain ⟨g, e, F, ik, φ, h⟩ := hpin j σ hj hσ
          exact ⟨D.sp.W_rank j hj.1 hj.2, g, e, F, ik, φ, th j σ hj hσ, (hι j hj).1, (hι j hj).2.1,
            hth j σ hj hσ, h⟩ }
  · exact
      { toLawsM := hM
        cuspMul := fun j _ => cusp_mul_of_M5 siegelSpaceAlgebra_holds (U j)
        latZ := fun j hj => hlatZ j _ hj h0
        cuNe := fun j hj => hcu j _ hj h0
        expo := fun j hj => hexpo j _ hj h0 }

end GlobalTheory.ExtCore
end


import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0062
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0052
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0057
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0054
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0015
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0022
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0040
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsHomOfLinearScalingHermForm
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EqZeroOfSumEmbeddingSmul
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0014
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0019
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0015
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.Bundle0001
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0036
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0021
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NumberFieldFinitePlaceCompletionEmbedding

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AllClassesOccur
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

theorem GlobalTheory.all_classes_occur :
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G G' : Matrix (Fin r) (Fin r) E), (∀ a b, FD.cc (G a b) = G b a) → (∀ a b, FD.cc (G' a b) = G' b a) → G.det ≠ 0 → G'.det ≠ 0 → (∀ τ : E →+* ℂ, ∃ p0 : ℕ, (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ FD.gram τ G Q = Matrix.diagonal fun a : Fin r => ((FD.sgn p0 (a : ℕ) : ℝ) : ℂ)) ∧ (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ FD.gram τ G' Q = Matrix.diagonal fun a : Fin r => ((FD.sgn p0 (a : ℕ) : ℝ) : ℂ))) → (∃ z : E, G'.det = z * FD.cc z * G.det) → ∃ ga : GL (Fin r) E, ∀ x y, FD.herm G ((ga : Matrix (Fin r) (Fin r) E) *ᵥ x) ((ga : Matrix (Fin r) (Fin r) E) *ᵥ y) = FD.herm G' x y) → (∀ (F : Type) [Field F] [NumberField F] (δ x : F), δ ≠ 0 → x ≠ 0 → (∀ σ : F →+* ℝ, ∃ a b : ℝ, σ x = a ^ 2 - σ δ * b ^ 2) → (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ∃ a b : v.adicCompletion F, algebraMap F (v.adicCompletion F) x = a ^ 2 - algebraMap F (v.adicCompletion F) δ * b ^ 2) → ∃ a b : F, x = a ^ 2 - δ * b ^ 2) → Out.Laws → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (t : SAB H (Sp k)) (g p : ℕ) (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ t.G)), 0 < p → IsProper t.G.hom → SmoothOfRelativeDimension g t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → (∀ x ∈ C, ∀ a, x ≫ t.act.act a ∈ C) → (∀ x ∈ C, x ^ p ^ 2 = 1) → (∀ x ∈ C, ∀ y ∈ C, Out.WeilIs t.G t.PP.L ((p ^ 2 : ℕ) : ℤ) x y 1) → Nat.card C = p ^ (2 * g) → ∃ (t' : SAB H (Sp k)) (ψ : t.G ⟶ t'.G), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L ∧ IsMonHom ψ ∧ IsFinite ψ.left ∧ Etale ψ.left ∧ Surjective ψ.left ∧ (∀ x : 𝟙_ (Over (Sp k)) ⟶ t.G, x ≫ ψ = 1 ↔ x ∈ C) ∧ (∀ a, t.act.act a ≫ ψ = ψ ≫ t'.act.act a) ∧ LBIso (lbPow t.PP.L (p ^ 2)) (t'.PP.L.pull ψ.left)) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty), l.A = 1 → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' : Datum H) (f : ℕ → D.La →ₗ[𝓞 E] D'.La), D'.p = D.p → D'.q = D.q → (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) → (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - D.EF a a') → ∃ (i : Fin U.n) (gam : D'.La ≃ₗ[𝓞 E] (U.Di i).La), (∀ a a', (U.Di i).EF (gam a) (gam a') = D'.EF a a') ∧ ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ e, gam (f l.M a) = U.t i a + l.M • e := by
  intro hL hN hLaw hQ E _ _ _ H D l Xo σ g ty U hA hσ hty D' f hp hq hf hE
  let i₀ : Fin U.n := ⟨0, U.n_pos⟩
  obtain ⟨hp₀, hq₀⟩ := U.sig i₀
  have hξ : FD.cc (H.rt : E) = -(H.rt : E) := by
    have h2 : (H.rt : E) ^ 2 = -(H.d : E) := by
      have := congrArg (fun a : 𝓞 E => (a : E)) H.rt_sq
      simpa using this
    have h3 : (FD.cc (H.rt : E)) ^ 2 = (H.rt : E) ^ 2 := by
      unfold FD.cc
      rw [← map_pow, h2, map_neg, map_natCast]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h3 with h | h
    · exfalso
      obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
      have h4 : starRingEnd ℂ (τ (H.rt : E)) = τ (H.rt : E) := by
        rw [← IsCMField.complexEmbedding_complexConj]
        exact congrArg τ h
      obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h4
      have h5 := congrArg τ h2
      rw [map_pow, hr, map_neg, map_natCast] at h5
      have h6 : r ^ 2 = -(H.d : ℝ) := by exact_mod_cast h5
      have h7 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
      nlinarith [sq_nonneg r]
    · exact h
  have hξ0 : (H.rt : E) ≠ 0 := by
    intro h
    have := congrArg (fun a : 𝓞 E => (a : E)) H.rt_sq
    simp only [h, RingOfIntegers.coe_eq_algebraMap, map_pow, map_neg, map_natCast] at this
    have h2 : (H.d : E) = 0 := by
      simpa using this
    exact H.d_prime.ne_zero (by exact_mod_cast h2)
  obtain ⟨Gm, φ, hφ⟩ := GlobalTheory.exists_herm_coord_of_datum E H (U.Di i₀) (H.rt : E) hξ hξ0 _ rfl
  obtain ⟨φ', hφ'⟩ := GlobalTheory.T.hermitian_forms_same_signature_same_space hL hN E H (U.Di i₀) D' _ _ Gm φ (hp.trans hp₀.symm) (hq.trans hq₀.symm) hξ hφ
  obtain ⟨hg, P₀, hP₀⟩ := (GlobalTheory.T.typeFn_period_exist_moduli_nonempty E H (U.Di i₀)).2.1 g ty (by rw [hp₀, hq₀]; exact hty)
  rw [hp₀, hq₀] at hg
  obtain ⟨N, j, j', P', hj, hP', h₁, h₂⟩ :=
    GlobalTheory.datum_commensurable_period E H (U.Di i₀) D' _ _ Gm φ φ' g ty hξ hφ hφ' P₀ hP₀
  obtain ⟨t₀, e₀, -, -, ht₀⟩ := GlobalTheory.T.exists_universal_fibre_uniformised_triple E H D l Xo σ g ty U i₀ P₀ hσ hg hP₀
  obtain ⟨t, e, ht⟩ := GlobalTheory.exists_uniformised_quotient_of_commensurable hLaw hQ E H (U.Di i₀) D' g ty P₀ P' N j j' t₀ e₀
    (hp.trans hp₀.symm) (hq.trans hq₀.symm) hj hP₀ hP' h₁ h₂ ht₀
  obtain ⟨o, m, hm⟩ := GlobalTheory.T.exists_obj_of_uniformised_triple_complex hLaw E H D D' l σ g ty P' t e f hA hσ hp hq hP' ht hf hE
  obtain ⟨y, ⟨hy, ⟨om⟩⟩, -⟩ := Xo.rep (Sp ℂ) (spMap σ) inferInstance o
  obtain ⟨i, P, hP, rfl⟩ := U.onto y hy
  obtain ⟨n, hn⟩ : ∃ n : SABMap t Xo.univ.t (U.u i P), n.φ = m.φ ≫ om.toSABMap.φ := by
    have := sabComp pullCubComp E H _ _ _ _ _ _ _ _ om.toSABMap m
    rwa [Category.id_comp] at this
  obtain ⟨h, gam, hh, hgam, hiso⟩ := GlobalTheory.T.familyUnif_fibre_lattice_eq_of_pullback E H D l Xo σ g ty U i P D' P' t e n hP hP' ht
  refine ⟨i, gam, hiso, fun a ha => ?_⟩
  have hM : (l.M : ℂ) ≠ 0 := by
    have := l.three_le
    exact_mod_cast (by omega : l.M ≠ 0)
  have k₁ : U.ex i P ((l.M : ℂ)⁻¹ • P (gam (f l.M a))) = U.ex i P ((l.M : ℂ)⁻¹ • P (U.t i a)) := by
    apply Over.OverMorphism.ext
    rw [← U.ex_eta i P hP a ha, hgam, ← map_smul, ← hh, hn, ← Category.assoc, hm a ha, om.eta, Over.comp_left]
    congr 1
  have k₂ : U.ex i P ((l.M : ℂ)⁻¹ • P (gam (f l.M a)) - (l.M : ℂ)⁻¹ • P (U.t i a)) = 1 := by
    have := U.ex_add i P hP ((l.M : ℂ)⁻¹ • P (gam (f l.M a)) - (l.M : ℂ)⁻¹ • P (U.t i a))
      ((l.M : ℂ)⁻¹ • P (U.t i a))
    rw [sub_add_cancel, k₁] at this
    exact (right_eq_mul.1 this)
  obtain ⟨b, hb⟩ := (U.ex_ker i P hP _).1 k₂
  refine ⟨b, hP.2.1 ?_⟩
  rw [map_add, map_nsmul, hb, ← Nat.cast_smul_eq_nsmul ℂ, ← smul_sub, smul_smul, mul_inv_cancel₀ hM, one_smul]
  abel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompConstMulMemHolSub
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompRat

namespace GlobalTheory.CompRat

theorem const_of_idem_on {Y : Type} [TopologicalSpace Y] {s : Set Y} (hs : IsPreconnected s) {g : Y → ℂ}
    (hg : ContinuousOn g s) (hi : ∀ x ∈ s, g x * g x = g x) : ∃ w : ℂ, ∀ x ∈ s, g x = w := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨x0, hx0⟩
  · exact ⟨0, fun _ h => h.elim⟩
  refine ⟨g x0, fun x hx => ?_⟩
  have hfin : (g '' s).Finite := by
    refine (Set.toFinite ({0, 1} : Set ℂ)).subset ?_
    rintro _ ⟨y, hy, rfl⟩
    have h := hi y hy
    have : g y * (g y - 1) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.1 h)
  exact hs.constant_of_mapsTo hfin.isDiscrete hg (Set.mapsTo_image g s) hx hx0

theorem rdU_mul_apply' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r)
    (f f' : Rul Xo c) (k : U.Comp) (x : Frame (U.X k).Ψ r) :
    rdU U (f * f') k x = rdU U f k x * rdU U f' k x := by
  by_cases h : x ∈ (U.X k).dom
  · have e1 : ∀ g : Rul Xo c, rdU U g k x = toC (evR Xo c g (U.un k ⟨x, h⟩)) := fun g => dif_pos h
    rw [e1, e1, e1]
    exact evalAt_mul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f f' (U.un k ⟨x, h⟩)
  · rw [rdU_mem_offZero U _ k x h, rdU_mem_offZero U f k x h, zero_mul]

end GlobalTheory.CompRat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompMulMemHolSub
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompRat

namespace GlobalTheory.CompRat

theorem compMul_mem_holSub {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}
    (X : Comp → Data E r) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (w : Comp → ℂ) {P : FDSec X}
    (hP : P ∈ holSub X la) : (fun k x => w k * P k x) ∈ holSub X la := by
  unfold holSub at hP
  induction hP using Submodule.span_induction with
  | mem Q hQ =>
    exact holCusp_mem_holSub X la fun k =>
      (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.2.2 (w k) (Q k) (hQ k)
  | zero =>
    have : (fun k x => w k * (0 : FDSec X) k x) = (0 : FDSec X) := by
      funext k x; simp
    rw [this]; exact Submodule.zero_mem _
  | add Q R _ _ hQ hR =>
    have : (fun k x => w k * (Q + R) k x) =
        ((fun k x => w k * Q k x) + (fun k x => w k * R k x) : FDSec X) := by
      funext k x; simp [mul_add]
    rw [this]; exact Submodule.add_mem _ hQ hR
  | smul a Q _ hQ =>
    have : (fun k x => w k * (a • Q) k x) = (a • (fun k x => w k * Q k x) : FDSec X) := by
      funext k x; simp [mul_left_comm]
    rw [this]; exact Submodule.smul_mem _ _ hQ

theorem holSub_compMul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Comp : Type) (X : Comp → Data E r) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (w : Comp → ℂ) (P : FDSec X), (P ∈ holSub X la → (fun k x => w k * P k x) ∈ holSub X la) ∧ (P ∈ holSub0 X la → (fun k x => w k * P k x) ∈ holSub0 X la) := by
  intro E _ _ _ r Comp X la w P
  refine ⟨compMul_mem_holSub X la w, fun h => ⟨compMul_mem_holSub X la w h.1, fun k x hx => ?_⟩⟩
  have h0 : P k x = 0 := h.2 k x hx
  show w k * P k x = 0
  rw [h0, mul_zero]

end GlobalTheory.CompRat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCmEndomorphismCommConjugation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CurveEndo

theorem scale_dual (f : ℂ →+* ℂ) (c : ℂ) :
    spMap (Chart.dualMapR f) ≫ spMap (epsScaleR c) = spMap (epsScaleR (f c)) ≫ spMap (Chart.dualMapR f) := by
  rw [spMap_comp_spMap, spMap_comp_spMap]
  congr 1
  ext a <;> simp [Chart.dualMapR, epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]

theorem dual_symm_dual (τ : ℂ ≃+* ℂ) :
    spMap (Chart.dualMapR (τ.symm : ℂ →+* ℂ)) ≫ spMap (Chart.dualMapR (τ : ℂ →+* ℂ)) = 𝟙 _ := by
  rw [spMap_comp_spMap]
  refine Eq.trans ?_ (Spec.map_id (CommRingCat.of (DualNumber ℂ)))
  congr 1
  ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

theorem left_eq_scale {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
    (he : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) {w : Fin g → ℂ} {v v' : epsR ℂ ⟶ A} (α : ℂ) (hv : IsTangent v)
    (hw : u.IsDiff w v) (hv' : IsTangent v') (hw' : u.IsDiff (α • w) v') :
    v'.left = spMap (epsScaleR α) ≫ v.left := by
  have hx := (LieMultiple.isLieComb_one_iff_comp α v _).2 rfl
  have hxt : IsTangent (Chart.spMap (Chart.scaleD α) ≫ v) :=
    (Chart.isTan_iff _).1 (Chart.isTan_scale α ((Chart.isTan_iff _).2 hv))
  rw [(he (α • w)).unique ⟨hv', hw'⟩ ⟨hxt, CMNormIdentity.isDiff_of_isLieComb u hw α hx⟩]
  exact (LieMultiple.isLieComb_one_iff α v _).1 hx

theorem comm_of_fixed (P : Out.PolAV (Sp ℂ)) (hg : P.g = 1) (u : HolUnif P.A P.L P.g)
    (hd : ∀ v, IsTangent v → ∃! w, u.IsDiff w v) (he : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v)
    (W : P.A ⟶ P.A) [IsMonHom W] (α : ℂ) (hW : ∀ z, u.ex (α • z) = u.ex z ≫ W)
    (τ : ℂ ≃+* ℂ) (hτ : τ α = α) (io : P.A.left ⟶ P.A.left) (h : IsGrpPullback P.A P.A (spMap (τ : ℂ →+* ℂ)) io) :
    W.left ≫ io = io ≫ W.left := by
  obtain ⟨W', hW', e⟩ := HomDescent.exists_isMonHom_pull h h W
  obtain ⟨v, ⟨hv, dv⟩, -⟩ := he (fun _ => 1)
  obtain ⟨v', hv', -⟩ := existsUnique_isVecOver h.1 v
  have tv' := hv'.isTangent h hv
  unfold IsVecOver at hv'
  obtain ⟨w', dw', -⟩ := hd v' tv'
  have h1 : (v ≫ W).left = spMap (epsScaleR α) ≫ v.left :=
    left_eq_scale u he α hv dv (HomLinear.isTangent_comp W hv)
      (HomLinear.isDiff_comp u u W (α • LinearMap.id) hW hv dv)
  have h2 : (v' ≫ W').left = spMap (epsScaleR α) ≫ v'.left := by
    refine h.1.hom_ext ?_ ?_
    · rw [Over.comp_left, Category.assoc, e, ← Category.assoc, hv', Category.assoc, ← Over.comp_left, h1,
        ← Category.assoc, scale_dual, Category.assoc, Category.assoc, hv']
      simp [hτ]
    · rw [Over.w, Category.assoc, Over.w]
      refine Eq.trans ?_ (spMap_comp_spMap _ _).symm
      show spMap _ = spMap _
      congr 1
      ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have hne : w' ≠ 0 := by
    rintro rfl
    have h3 := left_eq_scale u he 0 tv' dw' tv' (by rwa [zero_smul])
    have h4 : v.left = spMap (epsScaleR 0) ≫ v.left := by
      have h5 : spMap (Chart.dualMapR (τ : ℂ →+* ℂ)) ≫ v.left =
          spMap (Chart.dualMapR (τ : ℂ →+* ℂ)) ≫ spMap (epsScaleR 0) ≫ v.left := by
        rw [← Category.assoc, scale_dual, map_zero, Category.assoc, ← hv', ← Category.assoc, ← h3]
      have h6 := congrArg (spMap (Chart.dualMapR (τ.symm : ℂ →+* ℂ)) ≫ ·) h5
      simpa only [← Category.assoc, dual_symm_dual, Category.id_comp] using h6
    have h7 := (hd v hv).unique dv
      (CMNormIdentity.isDiff_of_isLieComb u dv 0 ((LieMultiple.isLieComb_one_iff 0 v v).2 h4))
    simpa using congrFun h7 ⟨0, by omega⟩
  obtain ⟨F, hF, -, hT, hu⟩ := HomLinear.exists_linear_of_isMonHom P.A P.A P.isAb P.isAb P.L P.L _ _ u u hd he W' hW'
  obtain ⟨tf, df⟩ := hT w' v' tv' dw'
  have h8 : F w' = α • w' := (hd _ tf).unique df
    (CMNormIdentity.isDiff_of_isLieComb u dw' α ((LieMultiple.isLieComb_one_iff α v' _).2 h2))
  have h9 : ∀ z, F z = α • z := fun z => by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
    have hz : z = (z i / w' i) • w' := by
      funext j
      have : j = i := Fin.ext (by have := j.2; have := i.2; omega)
      rw [this, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hi]
    rw [hz, map_smul, h8, smul_comm]
  rw [← e, ← hu W fun z => by rw [h9, hW]]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem cmHost_rootComplex_eq_pm_sqrt (H : Host E) : H.rt0 = Complex.I * Real.sqrt H.d ∨ H.rt0 = -(Complex.I * Real.sqrt H.d) := by
  rw [← sq_eq_sq_iff_eq_or_eq_neg, H.sqrt_neg_disc_sq, mul_pow, Complex.I_sq, ← Complex.ofReal_pow,
    Real.sq_sqrt (by positivity)]
  simp

theorem rt0_conj_neg_ne_zero (H : Host E) : starRingEnd ℂ H.rt0 = -H.rt0 := by
  rcases cmHost_rootComplex_eq_pm_sqrt H with h | h <;> rw [h] <;> simp

theorem mem_lattice (C : Curve H) (z : Fin C.P.g → ℂ) : z ∈ C.u.Λ ↔ ∃ a, z = fun _ => C.c * wC H a := by
  rw [C.lat z]
  rcases cmHost_rootComplex_eq_pm_sqrt H with h | h
  · exact ⟨fun ⟨m, n, e⟩ => ⟨(m, n), by rw [e, wC, h]⟩, fun ⟨a, e⟩ => ⟨a.1, a.2, by rw [e, wC, h]⟩⟩
  · refine ⟨fun ⟨m, n, e⟩ => ⟨(m + n, -n), ?_⟩, fun ⟨a, e⟩ => ⟨a.1 + a.2, -a.2, ?_⟩⟩
    · rw [e, wC, h]
      funext _
      push_cast
      ring
    · rw [e, wC, h]
      funext _
      push_cast
      ring

theorem exists_norm (H : Host E) : ∃ n : ℕ, (1 + H.d : ℂ) = 4 * n := by
  have := H.d_mod
  refine ⟨(1 + H.d) / 4, ?_⟩
  exact_mod_cast (by omega : 1 + H.d = 4 * ((1 + H.d) / 4))

theorem exists_endo_comm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (C : Curve H), ∃ W : C.P.A ⟶ C.P.A, IsMonHom W ∧ (∀ z, C.pt z ≫ W.left = C.pt (wC H (0, 1) * z)) ∧ (∀ z z', C.pt z = C.pt z' ↔ ∃ a, z - z' = wC H a) ∧ (∀ x : Sp ℂ ⟶ C.P.A.left, x ≫ C.P.A.hom = 𝟙 _ → ∃ z, C.pt z = x) ∧ ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∀ io : C.P.A.left ⟶ C.P.A.left, IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) io → W.left ≫ io = io ≫ W.left := by
  intro E _ _ _ H C
  obtain ⟨Hm, χ, Ef, hA, hd, he, hθ, -⟩ := C.theta
  obtain ⟨n, hn⟩ := exists_norm H
  have hsq := H.sqrt_neg_disc_sq
  have hα : wC H (0, 1) = (1 + H.rt0) / 2 := by simp [wC]
  obtain ⟨W, hW, hF⟩ := exists_hom_of_linear_scaling_hermForm C.P C.P C.u C.u Hm χ Hm χ hA hA
    (fun k => (hθ k).2) (fun k => (hθ k).1) (wC H (0, 1) • LinearMap.id) n
    (fun l hl => by
      obtain ⟨a, rfl⟩ := (mem_lattice C l).1 hl
      refine (mem_lattice C _).2 ⟨(-(n * a.2), a.1 + a.2), ?_⟩
      funext _
      simp only [LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply, smul_eq_mul, wC]
      push_cast
      linear_combination (C.c * a.2 / 4) * hsq - (C.c * a.2 / 4) * hn)
    (fun x y => by
      have e : wC H (0, 1) * starRingEnd ℂ (wC H (0, 1)) = n := by
        rw [hα, map_div₀, map_add, rt0_conj_neg_ne_zero, map_one, map_ofNat]
        linear_combination (-1 / 4 : ℂ) * hsq + (1 / 4 : ℂ) * hn
      simp only [LinearMap.smul_apply, LinearMap.id_apply, hermForm, star_smul, Matrix.mulVec_smul, smul_dotProduct,
        dotProduct_smul, smul_eq_mul]
      rw [← e, ← _root_.mul_assoc, _root_.mul_comm (wC H (0, 1))]
      rfl)
  refine ⟨W, hW, fun z => ?_, fun z z' => ?_, fun x hx => ?_, fun τ hτ io h => ?_⟩
  · unfold Curve.pt
    rw [← Over.comp_left, ← hF]
    congr 2
    funext _
    simp only [LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · have e := C.u.ex_add (fun _ => C.c * (z - z')) (fun _ => C.c * z')
    have e' : ((fun _ => C.c * (z - z')) + fun _ => C.c * z' : Fin C.P.g → ℂ) = fun _ => C.c * z := by
      funext _
      simp only [Pi.add_apply]
      ring
    rw [e'] at e
    have e₁ : C.pt z = C.pt z' ↔ C.u.ex (fun _ => C.c * z) = C.u.ex (fun _ => C.c * z') :=
      ⟨fun h => Over.OverMorphism.ext h, fun h => congrArg (fun t => t.left) h⟩
    rw [e₁, e, mul_eq_right, C.u.ker, mem_lattice]
    refine exists_congr fun a => ⟨fun h => ?_, fun h => by rw [h]⟩
    exact mul_left_cancel₀ C.c_ne (congrFun h ⟨0, by rw [C.g_eq]; omega⟩)
  · obtain ⟨z, hz⟩ := C.u.ex_onto (Over.homMk x hx)
    have hg := C.g_eq
    refine ⟨z ⟨0, by omega⟩ / C.c, ?_⟩
    have : (fun _ => C.c * (z ⟨0, by omega⟩ / C.c)) = z := by
      funext j
      rw [mul_div_cancel₀ _ C.c_ne]
      congr 1
      exact Fin.ext (by have := j.2; simp only; omega)
    unfold Curve.pt
    rw [this, hz]
    rfl
  · refine comm_of_fixed C.P C.g_eq C.u hd he W (wC H (0, 1)) hF τ ?_ io h
    rw [hα, map_div₀, map_add, hτ, map_one, map_ofNat]

end GlobalTheory.CurveEndo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLocalSectionNonzeroAllFibresModuliStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_section_nonzero_all_fibres_moduli : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (z : Xo.X), ∃ (R : Type) (_ : CommRing R) (_ : IsNoetherianRing R) (j : Sp R ⟶ Xo.X) (θ : LB.Sec (PPx j)), IsOpenImmersion j ∧ z ∈ Set.range j ∧ SecNZ j θ := by
  first | exact @GlobalTheory.PushLoc.exists_secNZ | exact GlobalTheory.PushLoc.exists_secNZ | (intros; apply GlobalTheory.PushLoc.exists_secNZ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsValuationSubringComplexComapValEq
section
namespace GlobalTheory

theorem exists_valuationSubring_complex_comap_val_eq (F : IntermediateField ℚ ℂ)
    (U : ValuationSubring F) (p : ℕ) (hp : (p : F) ∈ U.nonunits) :
    ∃ W : ValuationSubring ℂ, (p : ℂ) ∈ W.nonunits ∧ W.comap F.val.toRingHom = U := by
  obtain ⟨W, hW⟩ : ∃ W : ValuationSubring ℂ, W.comap (algebraMap F ℂ) = U :=
    exists_valuationSubring_comap_eq U _
  refine ⟨W, ?_, hW⟩
  rw [ValuationSubring.mem_nonunits_iff_or] at hp ⊢
  rcases hp with h | h
  · left
    simpa using congrArg (algebraMap F ℂ) h
  · right
    rw [← hW, ValuationSubring.mem_comap] at h
    simpa using h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExtendGenAndCorrOfGenericFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Exist

theorem extendGen : extendGenSt.{0} :=
  (GlobalTheory.cubical_extends_and_extendGen GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
    GlobalTheory.GenExtend.existsUnique_gen_extend).2

end GlobalTheory.Exist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FlagDomainModelsExponentsLevelMStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagDomainModels_exponents_levelM : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (r : ℕ) (M : ModelsOf F r) (ρ : ℕ), ModelBase M → l.A = 1 → FJ.ExpoMatch M.X 1 ρ l.M := by
  first | exact @GlobalTheory.ExpoModels.expoMatch_models | exact GlobalTheory.ExpoModels.expoMatch_models | (intros; apply GlobalTheory.ExpoModels.expoMatch_models <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ModuliExistsNumberFieldPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory

theorem moduli_exists_numberField_point :
    N1c → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → Formalism.L2.PjFree.XoNumPt Xo c := by
  intro hN E _ _ _ H Dw l Xo c hr
  obtain ⟨x⟩ := (PeriodExists.typeFn_period_exist E H Dw).2.2 hN hr l Xo c
  obtain ⟨L, _, _, hfin, y, hy, -⟩ := moduli_exists_algebraic_point E H Dw l Xo c ⊤ ⟨x, trivial⟩
  have : NumberField L := NumberField.of_module_finite c.F L
  refine ⟨L, inferInstance, this, algebraMap c.F L, y ≫ pullback.fst _ _, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, hy]
  simp only [sOf, spMap, ← Spec.map_comp]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NumberFieldFinitePlaceCompletionEmbeddingStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.numberField_finitePlace_completion_embedding : Formalism.L2.PjFree.LocFld := by
  first | exact @GlobalTheory.locFld | exact GlobalTheory.locFld | (intros; apply GlobalTheory.locFld <;> assumption)
end


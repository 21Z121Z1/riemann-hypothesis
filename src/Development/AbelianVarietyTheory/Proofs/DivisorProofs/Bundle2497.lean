import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2379
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2369
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0080
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2401
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2402
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2370
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2317
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2403
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0120
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnOfFixedOverUnramifiedExtension
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0035
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnAbelianLocusUniformisation
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2418
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitCocycleLiftObstruction
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.LBObs

theorem exists_isObU : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (u : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ), L.IsFun → UCoc F u → ∃ c, IsObU L α u c := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F L u hL hu
  have hmul : ∀ T (x y : L.B T), x ∈ I.map (algebraMap R (L.B T)) → y ∈ I.map (algebraMap R (L.B T)) →
      x * y = 0 := by
    intro T x y hx hy
    have h := Ideal.mul_mem_mul hx hy
    rw [← pow_two, ← Ideal.map_pow, hI, Ideal.zero_eq_bot, Ideal.map_bot] at h
    exact (Ideal.mem_bot).1 h
  have hv : ∀ (T T' : C) (a : T ⟶ T'), ∃ v : (L.B T')ˣ, L.p T' (v : L.B T') = (u T T' a : F.obj T') := by
    intro T T' a
    obtain ⟨x, hx⟩ := L.surj T' (u T T' a : F.obj T')
    obtain ⟨y, hy⟩ := L.surj T' (↑(u T T' a)⁻¹ : F.obj T')
    have hn : x * y - 1 ∈ I.map (algebraMap R (L.B T')) := by
      rw [← L.ker T', map_sub, map_mul, map_one, hx, hy, Units.mul_inv, sub_self]
    have hn2 := hmul T' _ _ hn hn
    exact ⟨⟨x, y * (1 - (x * y - 1)), by linear_combination (-1 : L.B T') * hn2,
      by linear_combination (-1 : L.B T') * hn2⟩, hx⟩
  choose v hvp using hv
  have hσ : ∀ T, ∃ σ : R₁ ⊗[R₀] F.obj T →+ L.B T, α.IsSig (L.p T) σ := fun T ↦
    exists_isSig R R₀ I hI π hπ hk R₁ α (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T) (L.ker T)
  choose σ hσ using hσ
  have hbas := fun T ↦ sig_basic R R₀ I hI π hπ hk R₁ α (L.B T) (F.obj T) (L.p T) (L.semi T) (L.surj T)
    (L.ker T) (σ T) (hσ T)
  have hz : ∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T''), ∃ y : R₁ ⊗[R₀] F.obj T'',
      α.KerQ y ∧ σ T'' y = L.ρ b (v T T' a : L.B T') * (v T' T'' b : L.B T'') * ↑(v T T'' (a ≫ b))⁻¹ - 1 := by
    intro T T' T'' a b
    refine (hbas T'').2.2.2 _ ?_
    have hpinv : L.p T'' ↑(v T T'' (a ≫ b))⁻¹ = ↑(u T T'' (a ≫ b))⁻¹ :=
      Units.eq_inv_of_mul_eq_one_left (by rw [← hvp, ← map_mul, Units.mul_inv, map_one])
    rw [← L.ker T'', map_sub, map_mul, map_mul, map_one, L.nat, hvp, hvp, hpinv, ← hu a b, Units.mul_inv, sub_self]
  choose z hzK hzσ using hz
  have heq : ∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T''),
      L.ρ b (v T T' a : L.B T') * (v T' T'' b : L.B T'') = (1 + σ T'' (z T T' T'' a b)) * (v T T'' (a ≫ b) : L.B T'') := by
    intro T T' T'' a b
    rw [hzσ, add_sub_cancel, mul_assoc _ _ (v T T'' (a ≫ b) : L.B T''), Units.inv_mul, _root_.mul_one]
  have hZ : (fun T T' T'' a b ↦ z T T' T'' a b : C2 (ext R₁ F)) ∈ Z2 (ext R₁ F) := by
    intro T T' T'' T''' a b c
    haveI := L.smooth T'''
    haveI : Module.Flat R (L.B T''') := Algebra.Smooth.flat R _
    have nat := sig_natural R R₀ I hI π hπ hk R₁ α (L.B T'') (F.obj T'') (L.p T'') (L.semi T'')
      (L.surj T'') (L.ker T'') (L.B T''') (F.obj T''') (L.p T''') (L.semi T''') (L.surj T''') (L.ker T''')
      (L.ρ c) (mp F c) (L.nat c) (σ T'') (σ T''') (hσ T'') (hσ T''')
    have em : ∀ y, mp (ext R₁ F) c y = extHom R₁ (mp F c) y := fun _ ↦ rfl
    rw [← sub_eq_zero]
    apply sig_inj_of_flat R R₀ I hI π hπ hk R₁ α (L.B T''') (F.obj T''') (L.p T''') (L.semi T''')
      (L.surj T''') (L.ker T''') (σ T''') (hσ T''')
    · have k1 := nat.2 _ (hzK T T' T'' a b)
      have k2 := hzK T T'' T''' (a ≫ b) c
      have k3 := hzK T T' T''' a (b ≫ c)
      have k4 := hzK T' T'' T''' b c
      unfold Aug.KerQ at k1 k2 k3 k4 ⊢
      rw [em]
      simp only [map_sub, map_add, k1, k2, k3, k4, sub_self, add_zero]
    · have m1 : L.ρ c (σ T'' (z T T' T'' a b)) ∈ I.map (algebraMap R (L.B T''')) := by
        rw [nat.1]; exact (hbas T''').1 _
      have m2 := (hbas T''').1 (z T T'' T''' (a ≫ b) c)
      have m3 := (hbas T''').1 (z T T' T''' a (b ≫ c))
      have m4 := (hbas T''').1 (z T' T'' T''' b c)
      have h12 := hmul T''' _ _ m1 m2
      have h43 := hmul T''' _ _ m4 m3
      have hA := congrArg (L.ρ c) (heq T T' T'' a b)
      rw [map_mul, map_mul, map_add, map_one] at hA
      have hB := heq T T'' T''' (a ≫ b) c
      have hC := heq T T' T''' a (b ≫ c)
      have hD := heq T' T'' T''' b c
      have hF := hL b c (v T T' a : L.B T')
      rw [Category.assoc] at hB
      rw [em, map_sub, map_add, map_add, ← nat.1]
      set E1 := L.ρ c (σ T'' (z T T' T'' a b))
      set E2 := σ T''' (z T T'' T''' (a ≫ b) c)
      set E3 := σ T''' (z T T' T''' a (b ≫ c))
      set E4 := σ T''' (z T' T'' T''' b c)
      set V := v T T''' (a ≫ b ≫ c)
      have hVW : (V : L.B T''') * ↑V⁻¹ = 1 := Units.mul_inv V
      have key1 : (1 + E1) * (1 + E2) * (V : L.B T''') = (1 + E4) * (1 + E3) * (V : L.B T''') := by
        linear_combination (-(1 + E1)) * hB - (v T'' T''' c : L.B T''') * hA + (1 + E4) * hC
          + L.ρ (b ≫ c) (v T T' a : L.B T') * hD
          - L.ρ c (v T' T'' b : L.B T'') * (v T'' T''' c : L.B T''') * hF
      have key2 : (1 + E1) * (1 + E2) = (1 + E4) * (1 + E3) := by
        linear_combination (↑V⁻¹ : L.B T''') * key1 - ((1 + E1) * (1 + E2) - (1 + E4) * (1 + E3)) * hVW
      linear_combination key2 - h12 + h43
  refine ⟨H2.mk _ ⟨_, hZ⟩, v, σ, ⟨_, hZ⟩, hvp, hσ, rfl, fun T T' T'' a b ↦ ⟨hzK T T' T'' a b, heq T T' T'' a b⟩⟩

end GlobalTheory.LBObs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalSectionBasesShrunkAffineChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.Poinc.exists_univBasis_affineChart : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U₀ : M.Z.Opens) (w : M.Z), IsAffineOpen U₀ → w ∈ U₀ → ∀ (P : PolAV (Sp (M.ringOn U₀))) (N : ℕ), 1 ≤ N → ∃ (U : M.Z.Opens) (h : M.ringOn U₀ ≤ M.ringOn U) (P' : PolAV (Sp (M.ringOn U))) (φ : P'.A.left ⟶ P.A.left), U ≤ U₀ ∧ IsAffineOpen U ∧ w ∈ U ∧ IsGrpPullback P'.A P.A (spMap (Subalgebra.inclusion h).toRingHom) φ ∧ LBIso P'.L (P.L.pull φ) ∧ P'.g = P.g ∧ (∃ th : LB.Sec (LPow P'.A P'.L 1 (baseOver (Sp (M.ringOn U)))), GlobalTheory.ThetaReal.UnivBasis P' 1 (fun _ : Fin 1 => SecM.ofSec P'.A th)) ∧ ∃ b : Fin (N ^ P'.g) → SecM P'.A P'.L (N : ℕ) (baseOver (Sp (M.ringOn U))), GlobalTheory.ThetaReal.UnivBasis P' (N : ℕ) b := by
  intro o Ω _ _ _ M U₀ w _ hw P N hN
  obtain ⟨hL, hL₂⟩ := GlobalTheory.abelianSchemeLaws_all
  have hle : M.ringOn U₀ ≤ M.O w := RatModel.ringOn_le_O hw
  let p : PrimeSpectrum (M.ringOn U₀) :=
    ⟨(IsLocalRing.maximalIdeal (M.O w)).comap (Subalgebra.inclusion hle).toRingHom, inferInstance⟩
  obtain ⟨V₁, m₁, b₁, hb₁⟩ := GlobalTheory.ThetaReal.exists_univBasis hL₂.secBaseChangeAny P 1 le_rfl p
  obtain ⟨V₂, m₂, b₂, hb₂⟩ := GlobalTheory.ThetaReal.exists_univBasis hL₂.secBaseChangeAny P N hN p
  obtain ⟨_, ⟨f, rfl⟩, hpf, hfV⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (u := ((V₁ ⊓ V₂ : (Sp (M.ringOn U₀)).Opens) : Set (Sp (M.ringOn U₀)))) (a := p) ⟨m₁, m₂⟩ (V₁ ⊓ V₂).isOpen
  have hfu : IsUnit (Subalgebra.inclusion hle f) := by
    by_contra hn
    exact hpf ((IsLocalRing.mem_maximalIdeal _).2 hn)
  obtain ⟨h0, hinv⟩ := (RatModel.isUnit_O_iff _).1 hfu
  obtain ⟨U, g, hU, hwU, hUU₀, hg⟩ := RatModel.exists_affine_of_mem_O hinv hw
  have h : M.ringOn U₀ ≤ M.ringOn U := RatModel.ringOn_anti (fun x hx => hUU₀ hx)
  have finv : ((f : Ω))⁻¹ ∈ M.ringOn U := (RatModel.mem_ringOn_iff_exists ⟨w, hwU⟩).2 ⟨g, hg⟩
  have hrange : ∀ V : (Sp (M.ringOn U₀)).Opens, V₁ ⊓ V₂ ≤ V →
      Set.range (spMap (Subalgebra.inclusion h).toRingHom) ⊆ V := by
    rintro V hV _ ⟨q, rfl⟩
    apply hV
    apply hfV
    show f ∉ (PrimeSpectrum.comap (Subalgebra.inclusion h).toRingHom q).asIdeal
    intro hq
    have hu : IsUnit (Subalgebra.inclusion h f) :=
      IsUnit.of_mul_eq_one ⟨_, finv⟩ (Subtype.ext (mul_inv_cancel₀ h0))
    exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hq hu)
  have fac : ∀ V : (Sp (M.ringOn U₀)).Opens, V₁ ⊓ V₂ ≤ V → ∃ τ : Sp (M.ringOn U) ⟶ (overRes (T := baseOver (Sp (M.ringOn U₀))) V).left,
      τ ≫ (overRes (T := baseOver (Sp (M.ringOn U₀))) V).hom = spMap (Subalgebra.inclusion h).toRingHom := fun V hV =>
    ⟨IsOpenImmersion.lift V.ι (spMap (Subalgebra.inclusion h).toRingHom) (by rw [Scheme.Opens.range_ι]; exact hrange V hV),
      by
        change _ ≫ V.ι ≫ 𝟙 _ = _
        rw [Category.comp_id, IsOpenImmersion.lift_fac]⟩
  obtain ⟨τ₁, hτ₁⟩ := fac V₁ inf_le_left
  obtain ⟨τ₂, hτ₂⟩ := fac V₂ inf_le_right
  obtain ⟨P', φ, hg, hφ, hiso⟩ := GlobalTheory.exists_isPolFibre hL.polBaseChange (Subalgebra.inclusion h).toRingHom P
  refine ⟨U, h, P', φ, hUU₀, hU, hwU, hφ, hiso.symm, hg, ?_, ?_⟩
  · obtain ⟨c₁, hc₁⟩ := GlobalTheory.T.universalBasis_move_baseChange _ _ _ P P' φ hφ hiso.symm _ _ _ τ₁ hτ₁ b₁ hb₁
    haveI : Unique (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
    have key : GlobalTheory.ThetaReal.UnivBasis P' ((1 : ℕ) : ℤ) (fun _ : Fin 1 => c₁ default) := by
      intro T hT u
      have h2 := @hc₁ T hT u
      obtain ⟨c, hc⟩ := h2
      exact ⟨c.reindex (finCongr (one_pow _)), fun i => (Module.Basis.reindex_apply c _ i).trans
        ((hc _).trans (congrArg _ (congrArg c₁ (Subsingleton.elim _ _))))⟩
    exact ⟨SecM.toSec P'.A (c₁ default), key⟩
  · obtain ⟨c₂, hc₂⟩ := GlobalTheory.T.universalBasis_move_baseChange _ _ _ P P' φ hφ hiso.symm _ _ _ τ₂ hτ₂ b₂ hb₂
    let e : Fin (N ^ P.g) ≃ Fin (N ^ P'.g) := finCongr (by rw [hg])
    refine ⟨fun i => c₂ (e.symm i), fun T hT u => ?_⟩
    have h2 := @hc₂ T hT u
    obtain ⟨c, hc⟩ := h2
    exact ⟨c.reindex e, fun i => (Module.Basis.reindex_apply c _ i).trans (hc _)⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendsToSemiAbelianOfLocallyNormalNoetherianStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extendsToSemiAbelian_of_locally_normal_noetherian : ∀ (X S : Scheme.{0}) [AlgebraicGeometry.IsNoetherian S], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ∀ (j : X ⟶ S) [IsOpenImmersion j], IsDominant j → ∀ (A : Over X) [GrpObj A], IsAbelianScheme A → (∀ s : S, ∃ U : S.Opens, s ∈ U ∧ HasExt (j ∣_ U) ((Over.pullback (j ⁻¹ᵁ U).ι).obj A)) → HasExt j A := by
  first | exact @GlobalTheory.ExtGlue.hasExt_of_locally | exact GlobalTheory.ExtGlue.hasExt_of_locally | (intros; apply GlobalTheory.ExtGlue.hasExt_of_locally <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorPowerTwoDiagonalAdditiveEqZeroProjectiveStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exteriorPowerTwo_diagonal_additive_eq_zero_projective : ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Module.Projective R M] (t : ⋀[R]^2 M), exteriorPower.map 2 (LinearMap.inl R M M + LinearMap.inr R M M) t = exteriorPower.map 2 (LinearMap.inl R M M) t + exteriorPower.map 2 (LinearMap.inr R M M) t → t = 0 := by
  first | exact @GlobalTheory.WedgeDiag.eq_zero_of_diag_additive | exact GlobalTheory.WedgeDiag.eq_zero_of_diag_additive | (intros; apply GlobalTheory.WedgeDiag.eq_zero_of_diag_additive <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorsFibreOverPointIffFactorsProduct
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistFlat

theorem factor_ker_iff {R : Type} [CommRing R] (A : Over (Sp R)) {T : Over (Sp R)} {V : Type} [CommRing V]
    (φ : Sp V ⟶ T.left) {H : Over (Sp R)} (h : H ⟶ A ⊗ T) (Y : Over (Sp V)) (x : Y ⟶ bc A φ) :
    (∃ y : Y ⟶ ker A φ h, y ≫ kerι A φ h = x) ↔
      ∃ z : up φ Y ⟶ H, z ≫ h = lift (upa φ x) (upt φ Y) := by
  constructor
  · rintro ⟨y, rfl⟩
    have hy : y.left ≫ pullback.snd (h ≫ snd A T).left φ = Y.hom := Over.w y
    have hT : (h ≫ snd A T).left ≫ T.hom = H.hom := Over.w _
    have hc : (y.left ≫ pullback.fst (h ≫ snd A T).left φ) ≫ (h ≫ snd A T).left = Y.hom ≫ φ := by
      rw [← hy]
      exact (Category.assoc _ _ _).trans
        ((congrArg (y.left ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm)
    refine ⟨Over.homMk (y.left ≫ pullback.fst (h ≫ snd A T).left φ) ?_, ?_⟩
    · show (y.left ≫ pullback.fst (h ≫ snd A T).left φ) ≫ H.hom = Y.hom ≫ φ ≫ T.hom
      rw [← hT, ← Category.assoc, hc, Category.assoc]
    · apply CartesianMonoidalCategory.hom_ext
      · rw [lift_fst, Category.assoc]
        apply Over.OverMorphism.ext
        have e : (kerι A φ h).left ≫ pullback.fst A.hom (φ ≫ T.hom)
            = pullback.fst (h ≫ snd A T).left φ ≫ (h ≫ fst A T).left := pullback.lift_fst _ _ _
        exact (Category.assoc _ _ _).trans
          ((congrArg (y.left ≫ ·) e.symm).trans (Category.assoc _ _ _).symm)
      · rw [lift_snd, Category.assoc]
        apply Over.OverMorphism.ext
        exact hc
  · rintro ⟨z, hz⟩
    have h1 : z ≫ h ≫ fst A T = upa φ x := by rw [← Category.assoc, hz, lift_fst]
    have h2 : z ≫ h ≫ snd A T = upt φ Y := by rw [← Category.assoc, hz, lift_snd]
    have h1' : z.left ≫ (h ≫ fst A T).left = x.left ≫ pullback.fst A.hom (φ ≫ T.hom) :=
      congrArg (·.left) h1
    have h2' : z.left ≫ (h ≫ snd A T).left = Y.hom ≫ φ := congrArg (·.left) h2
    let l : Y.left ⟶ pullback (h ≫ snd A T).left φ := pullback.lift z.left Y.hom h2'
    have l1 : l ≫ pullback.fst _ _ = z.left := pullback.lift_fst _ _ _
    have l2 : l ≫ pullback.snd _ _ = Y.hom := pullback.lift_snd _ _ _
    refine ⟨Over.homMk l l2, ?_⟩
    apply Over.OverMorphism.ext
    have e1 : (kerι A φ h).left ≫ pullback.fst A.hom (φ ≫ T.hom)
        = pullback.fst (h ≫ snd A T).left φ ≫ (h ≫ fst A T).left := pullback.lift_fst _ _ _
    have e2 : (kerι A φ h).left ≫ pullback.snd A.hom (φ ≫ T.hom)
        = pullback.snd (h ≫ snd A T).left φ := pullback.lift_snd _ _ _
    have hx : x.left ≫ pullback.snd A.hom (φ ≫ T.hom) = Y.hom := Over.w x
    apply pullback.hom_ext (f := A.hom) (g := φ ≫ T.hom)
    · refine (Category.assoc _ _ _).trans ((congrArg (l ≫ ·) e1).trans ?_)
      refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (h ≫ fst A T).left) l1).trans h1')
    · exact (Category.assoc _ _ _).trans ((congrArg (l ≫ ·) e2).trans (l2.trans hx.symm))

end GlobalTheory.TwistFlat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreIsoGrpPullbackIdentityTransport
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FibreTransport

theorem exists_compare {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G₁ G₂ : Over S'} [GrpObj G₁] [GrpObj G₂]
    {f₁ f₂ : S' ⟶ S} {φ₁ : G₁.left ⟶ G.left} {φ₂ : G₂.left ⟶ G.left} (h₁ : IsGrpPullback G₁ G f₁ φ₁)
    (h₂ : IsGrpPullback G₂ G f₂ φ₂) (hf : f₁ = f₂) :
    ∃ e : G₁.left ⟶ G₂.left, IsGrpPullback G₁ G₂ (𝟙 S') e ∧ e ≫ φ₂ = φ₁ := by
  subst hf
  refine ⟨h₂.1.lift φ₁ G₁.hom h₁.1.w, IsGrpPullback.cancel h₂ ?_ ?_, h₂.1.lift_fst _ _ _⟩
  · rw [h₂.1.lift_fst, Category.id_comp]; exact h₁
  · rw [h₂.1.lift_snd]; simp

theorem isGrpPullback_of_isIso {S : Scheme.{0}} {G₁ G₂ : Over S} [GrpObj G₁] [GrpObj G₂] (e : G₁ ⟶ G₂)
    [IsMonHom e] [IsIso e] : IsGrpPullback G₁ G₂ (𝟙 S) e.left := by
  haveI : IsIso e.left := inferInstanceAs (IsIso ((Over.forget S).map e))
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let k : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = k ≫ x ≫ e := Over.OverMorphism.ext (by simp [k, hx])
  have ey : y₀ = k ≫ y ≫ e := Over.OverMorphism.ext (by simp [k, hy])
  rw [ex, ey, ← MonObj.comp_mul, ← MonObj.mul_comp]
  simp [k]

theorem transport : ∀ (V V₁ K : Type) [CommRing V] [CommRing V₁] [Field K] (B : Over (Sp V)) [GrpObj B] (ρ : V →+* V₁) (ev : V₁ →+* K) (σ : K ≃+* K) (f₁ : (Over.pullback (spMap ev)).obj ((Over.pullback (spMap ρ)).obj B) ⟶ (Over.pullback (spMap (σ.toRingHom.comp ev))).obj ((Over.pullback (spMap ρ)).obj B)), IsMonHom f₁ → IsIso f₁ → ∃ f : ((Over.pullback (spMap (ev.comp ρ))).obj B).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj B).left, IsGrpPullback ((Over.pullback (spMap (ev.comp ρ))).obj B) ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj B) (𝟙 _) f ∧ ∀ (T : Scheme.{0}) (x : T ⟶ ((Over.pullback (spMap ev)).obj ((Over.pullback (spMap ρ)).obj B)).left) (y : T ⟶ ((Over.pullback (spMap (ev.comp ρ))).obj B).left), y ≫ pullback.fst B.hom (spMap (ev.comp ρ)) = x ≫ pullback.fst ((Over.pullback (spMap ρ)).obj B).hom (spMap ev) ≫ pullback.fst B.hom (spMap ρ) → y ≫ pullback.snd B.hom (spMap (ev.comp ρ)) = x ≫ pullback.snd ((Over.pullback (spMap ρ)).obj B).hom (spMap ev) → x ≫ f₁.left ≫ pullback.fst ((Over.pullback (spMap ρ)).obj B).hom (spMap (σ.toRingHom.comp ev)) ≫ pullback.fst B.hom (spMap ρ) = y ≫ f ≫ pullback.fst B.hom (spMap (σ.toRingHom.comp (ev.comp ρ))) := by
  intro V V₁ K _ _ _ B _ ρ ev σ f₁ hm hi
  have sp : ∀ t : V₁ →+* K, spMap (t.comp ρ) = spMap t ≫ spMap ρ := fun t => by
    simp only [spMap, ← Spec.map_comp]; rfl
  have two : ∀ t : V₁ →+* K, IsGrpPullback ((Over.pullback (spMap t)).obj ((Over.pullback (spMap ρ)).obj B)) B
      (spMap t ≫ spMap ρ) (pullback.fst ((Over.pullback (spMap ρ)).obj B).hom (spMap t) ≫ pullback.fst B.hom (spMap ρ)) :=
    fun t => (isGrpPullback_pullback _ (spMap t)).comp (isGrpPullback_pullback B (spMap ρ))
  obtain ⟨e₀, h₀, w₀⟩ := exists_compare (isGrpPullback_pullback B (spMap (ev.comp ρ))) (two ev) (sp ev)
  obtain ⟨e₁, h₁, w₁⟩ := exists_compare (two (σ.toRingHom.comp ev))
    (isGrpPullback_pullback B (spMap (σ.toRingHom.comp (ev.comp ρ)))) (sp (σ.toRingHom.comp ev)).symm
  refine ⟨e₀ ≫ f₁.left ≫ e₁, ?_, fun T x y hy₁ hy₂ => ?_⟩
  · have := h₀.comp ((isGrpPullback_of_isIso f₁).comp h₁)
    rwa [Category.id_comp, Category.id_comp] at this
  · have hx : x = y ≫ e₀ := by
      refine (two ev).1.hom_ext ?_ ?_
      · rw [Category.assoc, w₀]; exact hy₁.symm
      · rw [Category.assoc, h₀.1.w, Category.comp_id]; exact hy₂.symm
    rw [hx, Category.assoc, Category.assoc, Category.assoc, w₁]

end GlobalTheory.FibreTransport
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreSubsingletonOfClosedImmersionModIdealStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_subsingleton_of_closedImmersion_mod_ideal : ∀ (R : Type) [CommRing R] (I : Ideal R) (X Z : Scheme.{0}) (φ : X ⟶ Z) (p : Z ⟶ Spec (CommRingCat.of R)), IsClosedImmersion (((baseIdeal p I).comap φ).subschemeι ≫ φ) → ∀ z : Z, I ≤ (p z).asIdeal → (⇑φ ⁻¹' {z}).Subsingleton := by
  first | exact @GlobalTheory.FormalAlg.fibre_subsingleton_of_isClosedImmersion_restrict | exact GlobalTheory.FormalAlg.fibre_subsingleton_of_isClosedImmersion_restrict | (intros; apply GlobalTheory.FormalAlg.fibre_subsingleton_of_isClosedImmersion_restrict <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCodimOnePointsClosed
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Cartier

theorem finite_coheight_one_of_ne_top : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsNoetherian Y]
    (B : Closeds Y), B ≠ ⊤ → {v : Y | Order.coheight v = 1 ∧ v ∈ B}.Finite := by
  intro Y _ _ B hB
  classical
  have hgen : genericPoint Y ∉ (B : Set Y) := fun h =>
    hB (eq_top_iff.2 fun x _ => (genericPoint_specializes x).mem_closed B.isClosed h)
  obtain ⟨S, hS, hc, hi, hU⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible B.isClosed
  refine (hS.image fun T => if h : IsIrreducible T then h.genericPoint else genericPoint Y).subset
    fun z hz => ?_
  obtain ⟨T, hT, hzT⟩ := Set.mem_sUnion.1 (hU.le hz.2)
  refine ⟨T, hT, ?_⟩
  simp only [dif_pos (hi T hT)]
  have hg := (hi T hT).isGenericPoint_genericPoint (hc T hT)
  have h₁ : z ≤ (hi T hT).genericPoint := hg.specializes hzT
  have h₂ : (hi T hT).genericPoint < genericPoint Y := by
    refine lt_of_le_not_ge (genericPoint_specializes _) fun e => ?_
    have e' : _ = genericPoint Y := (Specializes.antisymm e (genericPoint_specializes _)).eq
    exact hgen (e' ▸ hU.ge (Set.mem_sUnion.2 ⟨T, hT, hg.mem⟩))
  by_contra hne
  have h₃ := Order.coheight_add_one_le (lt_of_le_not_ge h₁ fun e =>
    hne (Specializes.antisymm h₁ e).eq)
  have h₄ := Order.coheight_add_one_le h₂
  rw [hz.1] at h₃
  have h₅ : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add_left (le_add_self.trans h₄) 1).trans h₃
  exact absurd h₅ (by decide)

end GlobalTheory.Cartier
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFaithfullyFlatAlgebraOverAffineOpenStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_faithfullyFlat_algebra_over_affine_open : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] [Flat f] [Surjective f] [IsLocallyNoetherian Y] (V₀ : Y.Opens), IsAffineOpen V₀ →
    letI : Algebra Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀) := (f.app V₀).hom.toAlgebra
    IsNoetherianRing Γ(Y, V₀) ∧ Module.Finite Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀) ∧ Module.FaithfullyFlat Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀) := by
  first | exact @GlobalTheory.finiteFlatSurj_affine_algebra | exact GlobalTheory.finiteFlatSurj_affine_algebra | (intros; apply GlobalTheory.finiteFlatSurj_affine_algebra <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFibreCorrespondenceOfIsFiniteFirstStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_fibre_correspondence_of_isFinite_first : ∀ (X Y₀ Y : Scheme.{0}) (s t : Y ⟶ X) (i : Y₀ ⟶ Y), IsFinite s → IsOpenImmersion i → IsDominant i → IsLocallyNoetherian Y → (∀ z : X, {u : X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ i ≫ s ∧ spMap (algebraMap V K) ≫ z' = x ≫ i ≫ t ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}.Finite) → ∀ z : X, {y : Y | t y = z}.Finite := by
  first | (exact @GlobalTheory.FibreCrit.finite_fibre_of_isFinite) | (exact GlobalTheory.FibreCrit.finite_fibre_of_isFinite) | (intros; apply GlobalTheory.FibreCrit.finite_fibre_of_isFinite  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteKTorsionAbelianPartAlgClosed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.AbTorsionFiniteF

theorem finite_torsion_TF : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → Finite {x : TF (R := R) F ⟶ D.P.A // x ^ k = 1} := by
  intro R _ _ D F _ _ _ k hk
  let g := jFK (R := R) F ≫ jK R
  let B' := (Over.pullback g).obj D.P.A
  have hB : IsAbelianScheme B' := GlobalTheory.isAbelianScheme_pullback_obj g D.P.A D.P.isAb
  have hfin := GlobalTheory.AbTorsionFinite.finite_torsion F B' hB k hk
  let φ : (TF (R := R) F ⟶ D.P.A) → (𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ B') := fun x =>
    Over.homMk (pullback.lift x.left (𝟙_ (Over (Spec (CommRingCat.of F)))).hom
      ((Over.w x).trans (by simp [g]))) (pullback.lift_snd _ _ _)
  have hφ : ∀ x, (φ x).left ≫ pullback.fst D.P.A.hom g = x.left := fun x => pullback.lift_fst _ _ _
  have hpow : ∀ x : TF (R := R) F ⟶ D.P.A, (φ x) ^ k = 1 ↔ x ^ k = 1 := fun x =>
    GlobalTheory.PsiAbelian.pow_eq_one_iff_of_pull (by simp [g]) (isGrpPullback_pullback D.P.A g) (hφ x)
  refine Finite.of_injective (fun x : {x : TF (R := R) F ⟶ D.P.A // x ^ k = 1} =>
    (⟨φ x.1, (hpow x.1).2 x.2⟩ : {y : 𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ B' // y ^ k = 1})) ?_
  intro a b hab
  have e := congrArg (fun y => y.1.left ≫ pullback.fst D.P.A.hom g) hab
  simp only [hφ] at e
  exact Subtype.ext (Over.OverMorphism.ext e)

end GlobalTheory.AbTorsionFiniteF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSectionOverOrdinaryLocus
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES.CorrQF

theorem finite_specialisations_of_finite_open {R : Type} [CommRing R] {X : Scheme.{0}} (sX : X ⟶ Sp R)
    [IsSeparated sX] (U : X.Opens) (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ X) (gs : Y₀ ⟶ U.toScheme)
    (hgs : gs ≫ U.ι = s₀) [IsFinite gs] (u : X) (hu : u ∈ U) :
    {z : X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K)
      (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ X) (x : Sp K ⟶ Y₀),
      spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧
      y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}.Finite := by
  have hF : (s₀.base ⁻¹' {u}).Finite := by
    refine (gs.finite_preimage_singleton (⟨u, hu⟩ : U)).subset fun y hy => ?_
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hy ⊢
    apply U.ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, hgs, hy]
    rfl
  refine (hF.image t₀.base).subset ?_
  rintro z ⟨V, K, _, _, _, _, _, _, y', z', x, h1, h2, h3, h4⟩
  have hrange : Set.range y'.base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint (R := V) w).map y'.continuous).mem_open U.isOpen (h3 ▸ hu)
  have hy''f : IsOpenImmersion.lift U.ι y' hrange ≫ U.ι = y' := IsOpenImmersion.lift_fac _ _ _
  have hE : ValuativeCriterion.Existence gs :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed gs) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) gs).1
  have hw : x ≫ gs = Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ IsOpenImmersion.lift U.ι y' hrange := by
    rw [← cancel_mono U.ι, Category.assoc, hgs, Category.assoc, hy''f]
    exact h1.symm
  obtain ⟨⟨l, hl1, hl2⟩⟩ :=
    (hE { R := V, K := K, i₁ := x, i₂ := IsOpenImmersion.lift U.ι y' hrange, commSq := ⟨hw⟩ }).exists_lift
  have hl1' : spMap (algebraMap V K) ≫ l = x := hl1
  have hl2' : l ≫ gs = IsOpenImmersion.lift U.ι y' hrange := hl2
  have : IsDominant (spMap (algebraMap V K)) :=
    ⟨PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _ |>.2 (by
      exact ((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V K)).le.trans bot_le)⟩
  have hlz : l ≫ t₀ = z' := by
    refine ext_of_isDominant_of_isSeparated (sX ≫ spMap (algebraMap ℤ R)) ?_ (spMap (algebraMap V K)) ?_
    · exact specZIsTerminal.hom_ext _ _
    · rw [reassoc_of% hl1', h2]
  refine ⟨l (IsLocalRing.closedPoint V), ?_, ?_⟩
  · simp only [Set.mem_preimage, Set.mem_singleton_iff]
    have hc : (l ≫ gs ≫ U.ι) (IsLocalRing.closedPoint V) = y' (IsLocalRing.closedPoint V) := by
      rw [reassoc_of% hl2', hy''f]
    calc s₀ (l (IsLocalRing.closedPoint V)) = (l ≫ gs ≫ U.ι) (IsLocalRing.closedPoint V) := by
          rw [hgs]; first | rfl | simp
      _ = u := hc.trans h3
  · rw [← h4, ← hlz]
    first | rfl | simp

theorem isSeparated_structure_morphism_model {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    (M : Model b N) : IsSeparated M.s := by
  obtain ⟨n, i, hi, -, e⟩ := M.qproj
  have := isProper_str R n
  rw [← e]
  infer_instance

theorem finite_specialisations_of_finite_source : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (M : Model b N) (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (gs : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme), gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → IsFinite gs → ∀ u : M.X, u ∈ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))) → {z : M.X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}.Finite := by
  intro p _ D R _ b N M Y₀ s₀ t₀ gs hgs hfin u hu
  have := isSeparated_structure_morphism_model M
  exact finite_specialisations_of_finite_open M.s _ Y₀ s₀ t₀ gs hgs u hu

end GlobalTheory.UPel.HT.ES.CorrQF
end
end


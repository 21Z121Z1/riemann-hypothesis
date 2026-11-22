import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1150
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0732
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0683
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0751
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0750
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0264
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0262
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0269
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1333
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import Formalism.HarderNarasimhan.StatementPl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1334
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1092
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0986
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1326
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceLatticeFractionalMultipleAgree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0017
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0023
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1267
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1301
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1336
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1331
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1306
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1262
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1266
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1335
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterEmbeddingCompat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0171
import Formalism.LocalToGlobal.HermitianColumns.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0081
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0183

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSphericalOfIsCompAlongSplit
section
open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SphBC

open GlobalTheory.PRep GlobalTheory.DefU

theorem isSpherical_of_isCompAlong_split {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
    {π : Submodule ℂ (UA E n → ℂ)} (hπ : IsAutRepU π) {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w)
    {X : Type} [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) X)
    (hc : IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) σ) (hu : IsUnramU π w) :
    GlobalTheory.LGrp.IsSpherical σ (GlobalTheory.LFun.KGL w n) := by
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E n w hw
  have hp : Function.Surjective ((cLoc w).comp (locU n w).subtype) := fun g =>
    ⟨e.symm g, (he _).symm.trans (e.apply_symm_apply g)⟩
  obtain ⟨φ, hφ, hφ0, hφK⟩ := hu
  by_contra hns
  have hfix : ∀ v, (∀ k ∈ GlobalTheory.LFun.KGL w n, σ k v = v) → v = 0 := by
    intro v hv
    by_contra hv0
    exact hns ((Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.LGrp.mem_fixed.2 hv, hv0⟩)
  obtain ⟨hσirr, f, hf0, hfm, hf⟩ := hc
  let Ψ : AutSub E n := ⟨π, hπ⟩
  have hirr : Representation.IsIrreducible (σ.comp ((cLoc w).comp (locU n w).subtype)) := by
    obtain ⟨h0, h1⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 hσirr
    refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun Y hY => h1 Y fun g v hv => ?_⟩
    obtain ⟨x, rfl⟩ := hp g
    exact hY x v hv
  let F : Representation.IntertwiningMap (σ.comp ((cLoc w).comp (locU n w).subtype)) (Ψ.rep.comp (locU n w).subtype) :=
    ⟨f.codRestrict _ hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf x v)⟩
  have hF0 : F ≠ 0 := fun h => hf0 (LinearMap.ext fun v => by
    have := congrArg Subtype.val (DFunLike.congr_fun h v)
    exact this)
  obtain ⟨r, -, -, hr⟩ := GlobalTheory.DefU.LocRet.exists_ret E n w
  have htop := (GlobalTheory.CuspRep.CompUniq.isotypic (UA E n) (locU n w) Ψ.V X X Ψ.rep (locU n w).subtype
    (σ.comp ((cLoc w).comp (locU n w).subtype)) (σ.comp ((cLoc w).comp (locU n w).subtype))
    Ψ.isIrreducible_rep hirr hirr (fun g => ⟨r g, fun y => hr g y⟩) F hF0).1
  let fi : Representation.IntertwiningMap (σ.comp ((cLoc w).comp (locU n w).subtype))
      (Ψ.rep.comp (locU n w).subtype) → X →ₗ[ℂ] (UA E n → ℂ) := fun i => π.subtype ∘ₗ i.toLinearMap
  have hfi : ∀ i g u, fi i ((σ.comp ((cLoc w).comp (locU n w).subtype)) g u) =
      (RU E n).comp (locU n w).subtype g (fi i u) := fun i g u =>
    congrArg Subtype.val (Representation.IntertwiningMap.isIntertwining _ _ i g u)
  have hmem : φ ∈ ⨆ i, LinearMap.range (fi i) := by
    have : φ ∈ (⨆ i : Representation.IntertwiningMap (σ.comp ((cLoc w).comp (locU n w).subtype))
        (Ψ.rep.comp (locU n w).subtype), LinearMap.range i.toLinearMap).map π.subtype := by
      rw [htop]; exact ⟨⟨φ, hφ⟩, Submodule.mem_top, rfl⟩
    simp only [fi, LinearMap.range_comp]
    rwa [Submodule.map_iSup] at this
  have key := GlobalTheory.InertHeckeEigen.mem_of_mem_iSup ((RU E n).comp (locU n w).subtype)
    (σ.comp ((cLoc w).comp (locU n w).subtype)) hirr fi hfi
    (((GlobalTheory.LFun.KGL w n).comap ((cLoc w).comp (locU n w).subtype) : Subgroup (locU n w)) : Set (locU n w)) ⊥
    (fun i v hv => by
      have hv' : v = 0 := hfix v fun k hk => by
        obtain ⟨x, rfl⟩ := hp k
        exact hv x hk
      rw [hv', map_zero]
      exact Submodule.zero_mem _)
    (fun z hz _ _ => by rw [(Submodule.mem_bot ℂ).1 hz, map_zero]) φ (fun k hk => hφK k.1 k.2 hk) hmem
  exact hφ0 ((Submodule.mem_bot ℂ).1 key)

theorem isSpherical_of_isUnramU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π →
    ∀ (c : ℕ) (a d : Fin c → ℕ) (h : ∑ i, d i * a i = n) (P : ∀ i, CuspSub E (a i))
      (ρ : ∀ i (w : HeightOneSpectrum (𝓞 E)), LocIrr w (a i)) (m : Fin c → (E →+* ℂ) → Multiset ℂ)
      (σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), LocIrr w (d i * a i)),
      GlobalTheory.BcSpeh.Parts π a d h P ρ m →
      (∀ i w, IsUnitarisable (ρ i w).ρ ∧ IsUnitarisable (σ i w).ρ ∧
        GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of (ρ i w).ρ (ρ i w).smooth (ρ i w).irred) (d i) (σ i w).ρ) →
      (∀ w, IsSplitAt w → IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd h w (σ · w))) →
      ∀ w, IsUnramU π w → ∀ i (τ : SmIrr (GL (Fin (a i)) (w.adicCompletion E))), (P i).IsLocComp w τ →
        GlobalTheory.LGrp.IsSpherical τ.ρ (GlobalTheory.LFun.KGL w (a i)) := by
  intro E _ _ _ hE n π hπ c a d h P ρ m σ hp hsh hsplit w hu i τ hτ
  suffices hB : ∃ B, GlobalTheory.LFun.HasSatGL w (ρ i w).ρ B by
    obtain ⟨B, hB⟩ := hB
    have h1 := (GlobalTheory.BcSpehCompare.hasSat_iff (hp.loc i w) B).2 hB
    exact ((GlobalTheory.BcSpehCompare.hasSat_iff hτ B).1 h1).1
  by_cases hw : IsSplitAt w
  · have hc := hsplit w hw
    have hs : GlobalTheory.LGrp.IsSpherical (locProd h w (σ · w)) (GlobalTheory.LFun.KGL w n) :=
      isSpherical_of_isCompAlong_split hπ hw _ hc hu
    have hsm : GlobalTheory.PRep.IsSmooth (locProd h w (σ · w)) := GlobalTheory.SmGL.isSmooth_parInd _ _
    have hirr : (locProd h w (σ · w)).IsIrreducible := hc.1
    obtain ⟨T, hT⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible hsm hirr hs
    obtain ⟨S, hS, -⟩ := GlobalTheory.SatInd.satake_locProd_speh E w c n a d h (ρ · w) (σ · w) (fun i => (hp.pos i).2)
      (fun i => (hsh i w).2.2) T hT
    exact ⟨S i, hS i⟩
  · obtain ⟨s, ϖ, q, α, h1, h2, h3⟩ := GlobalTheory.BcSpehCompare.exists_hasSatAt hE hπ hw hu
    obtain ⟨S, hS, -⟩ := hp.inert w s ϖ q h1 h2 α h3
    exact ⟨S i, hS i⟩

end GlobalTheory.SphBC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingNumberFieldTwistStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kawamataViehweg_vanishing_numberField_twist : Quoted → ∀ (K : Type) [Field K] [NumberField K] (G : Geo K), IsNef K G.LA → IsBig K G.LA → VanishFrom G.L (GlobalTheory.LB.toMod (tens G.K.bundle G.LA)) 0 := by
  first | exact @GlobalTheory.HSCore.VanishNumberField.vanishFrom_adj | exact GlobalTheory.HSCore.VanishNumberField.vanishFrom_adj | (intros; apply GlobalTheory.HSCore.VanishNumberField.vanishFrom_adj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzPairFormRatioLocalScalarNormStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kottwitzPair_form_ratio_local_scalar_norm : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → (∀ g, f g ≠ 0 → RegAf G g) → ∀ P₁ : Pair G, ∃ S : Finset ℕ, ∀ (P : Pair G), P.γ = P₁.γ → P.c = P₁.c → ∀ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (g : G.GAf), f (g⁻¹ * P.toAf x t hx P.self * g) ≠ 0 → ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∉ S → ∃ (u : ℚ_[ℓ]ˣ) (z : (ℚ_[ℓ] ⊗[ℚ] G.C)ˣ), Commute (z : ℚ_[ℓ] ⊗[ℚ] G.C) (inC G ℚ_[ℓ] (P₁.γ : G.C)) ∧ inC G ℚ_[ℓ] ((P.β : G.C) * ((P₁.β⁻¹ : G.Cˣ) : G.C)) = algebraMap ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] G.C) (u : ℚ_[ℓ]) * ((z : ℚ_[ℓ] ⊗[ℚ] G.C) * inC G ℚ_[ℓ] (P₁.β : G.C) * (starT G.star ℚ_[ℓ] (z : ℚ_[ℓ] ⊗[ℚ] G.C)).unop * inC G ℚ_[ℓ] ((P₁.β⁻¹ : G.Cˣ) : G.C)) := by
  first | (exact @GlobalTheory.CxRegPair.local_pair_scalar_norm) | (exact GlobalTheory.CxRegPair.local_pair_scalar_norm) | (intros; apply GlobalTheory.CxRegPair.local_pair_scalar_norm  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCongruenceEndomorphism
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GeoLevel

section General

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix

theorem exists_endo_approx_of_keeps_hat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n : ℕ} (L Λ : Submodule (𝓞 E) (Fin n → E)) (g : GL (Fin n) (RA F E)) (h1 : L.FG)
    (h2 : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (hΛ : (Λ : Set (Fin n → E)) = latOf F (g : Matrix (Fin n) (Fin n) (RA F E)) L)
    (hg : ∀ z ∈ hat F (L : Set (Fin n → E)), (g : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ z ∈ hat F (L : Set (Fin n → E)))
    {La : Type} [AddCommGroup La] [Module (𝓞 E) La] (ι : La →ₗ[𝓞 E] (Fin n → E)) (hi : Function.Injective ι)
    (hr : LinearMap.range ι = L) (N : ℕ) (hN : 0 < N) :
    ∃ γ₀ : La →ₗ[𝓞 E] La, ∀ a, ∃ w ∈ hat F (L : Set (Fin n → E)),
      (g : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ (fv F (ι a)) - fv F (ι (γ₀ a)) = N • w := by
  subst hr
  obtain ⟨f, hf, -, -⟩ := exists_linear_approx_tower F E n _ g Λ h1 h2 hΛ
  have hle : Λ ≤ LinearMap.range ι := by
    intro v hv
    have hv' : v ∈ (Λ : Set (Fin n → E)) := hv
    rw [hΛ] at hv'
    obtain ⟨z, hz, hzv⟩ := hv'
    refine ((hat_rational_points_and_approx F E n _ h1 h2).1 v).1 ?_
    rw [← hzv]
    exact hg z hz
  let e : La ≃ₗ[𝓞 E] LinearMap.range ι := LinearEquiv.ofInjective ι hi
  have he : ∀ x : LinearMap.range ι, ι (e.symm x) = x := fun x => by
    have : ((e (e.symm x) : LinearMap.range ι) : Fin n → E) = x := by rw [e.apply_symm_apply]
    exact this
  refine ⟨e.symm.toLinearMap ∘ₗ Submodule.inclusion hle ∘ₗ f N ∘ₗ e.toLinearMap, fun a => ?_⟩
  obtain ⟨w, hw, hfw⟩ := hf N hN (e a)
  refine ⟨-((g : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ w), neg_mem (hg w hw), ?_⟩
  have h3 : ι ((e.symm.toLinearMap ∘ₗ Submodule.inclusion hle ∘ₗ f N ∘ₗ e.toLinearMap) a) =
      (f N (e a) : Fin n → E) := he _
  have h4 : ((e a : LinearMap.range ι) : Fin n → E) = ι a := rfl
  rw [h3, hfw, h4, Matrix.mulVec_add, GlobalTheory.AdLat.Tower.mulVec_nsmul, smul_neg]
  abel

end General

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts GlobalTheory.GeoLevel
open GlobalTheory.Member (FinCong IotaOK)
open GlobalTheory.LevelCusp (IsMatch)
open GlobalTheory.Dict (castFr)
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

theorem exists_endo_approx : ∀ (D : D7) (V : HSp D) (La : Type) [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), LatEmb V ι → ∀ (N : ℕ), 0 < N → ∀ κ : GA D V, FinCong V 1 κ → ∃ γ₀ : La →ₗ[𝓞 D.host.E] La, ∀ a, ∃ w ∈ latGHat V 1, (finHom V κ).1.mulVec (finVec V (ι a)) - finVec V (ι (γ₀ a)) = N • w := by
  intro D V La _ _ ι hι N hN κ hκ
  obtain ⟨h1, h2, -, -, h5, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D V 1
  obtain ⟨-, -, h3, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D V κ
  have hk := (GlobalTheory.Member.AALev.congruences_agree D V κ).1.2 hκ
  rw [h5] at hk ⊢
  exact exists_endo_approx_of_keeps_hat (F := D.host.F) (latG V 1) (latG V κ) (finHom V κ) h1 h2 h3 hk ι hι.1 hι.2 N hN

end GlobalTheory.GeoLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevOpParabEqLevOpCt
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.LeviFubini
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

end GlobalTheory.LeviFubini

namespace GlobalTheory.LeviFubini
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem absHalf_eq_deltaHalf {a b : ℕ} (w : Pl E) (m : GLw a w × GLw b w) :
    absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) =
      (GlobalTheory.SmGL.deltaHalf (w.adicCompletion E) (GlobalTheory.SmGL.Two (Fin a) (Fin b))
        (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b) m) : ℂ) := GlobalTheory.T.modulus_half_levi_abs_det E a b w m

theorem hint_eq_level {H : Type} [Group H] (K L : Subgroup H) (u : H → ℂ) (hLK : L ≤ K) (hLu : L ≤ rStab u)
    (hfin : L.relIndex K ≠ 0) : hint K u = ((L.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ q : H ⧸ L, u q.out :=
  GlobalTheory.T.haarIntegralNormalizedOpenCompact_eq_finite_level_sum H K L u hLK hLu hfin

theorem deltaHalf_eq_one {a b : ℕ} (w : Pl E) (m : GLw a w × GLw b w) (h1 : m.1 ∈ GlobalTheory.LFun.KGL w a) (h2 : m.2 ∈ GlobalTheory.LFun.KGL w b) :
    GlobalTheory.SmGL.deltaHalf (w.adicCompletion E) (GlobalTheory.SmGL.Two (Fin a) (Fin b))
                 (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b) m) = 1 := GlobalTheory.T.modulus_levi_maximal_compact_one E a b w m h1 h2

theorem int_points {a b n : ℕ} (h : a + b = n) (w : Pl E) :
    ((GlobalTheory.LFun.KGL w n).subgroupOf (parB h w)).comap (uN h w) = intMat a b w ∧
      ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)).map (sM h w) ≤ (GlobalTheory.LFun.KGL w n).subgroupOf (parB h w) :=
  GlobalTheory.T.maximal_compact_parabolic_unipotent_eq E a b n h w

end GlobalTheory.LeviFubini

namespace GlobalTheory.LeviFubini
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

end GlobalTheory.LeviFubini

namespace GlobalTheory.LeviFubini

end GlobalTheory.LeviFubini
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelGroupLiftExists
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts GlobalTheory.GeoLevel
open GlobalTheory.Member (FinCong IotaOK)
open GlobalTheory.LevelCusp (IsMatch)
open GlobalTheory.Dict (castFr)
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GeoLevel

theorem isBaseFrame_of_isLatBasis {D : D7} (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (h : IsLatBasis V rfl β) :
    IsBaseFrame V β (GlobalTheory.Member.latC V) 1 := by
  refine ⟨fun x => ?_, Formalism.L2.Herm.coordinate_lattice_self_dual D.sp.cm V, Nat.one_pos, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨z, rfl⟩ := GlobalTheory.LiftLevel.swap_surj x
    refine Iff.trans ?_ (h z)
    rw [(GlobalTheory.Member.latHat_eq_hat_and_gram D V).1]
    exact (GlobalTheory.LevSplit.latHat_iff _ z).symm
  · rw [← GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq] at hx
    simpa using hx
  · rw [← GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq]
    simpa using hx

theorem not_isConjPl_of_le {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (l : Level H)
    {w w' : Formalism.L2.DIV.Pl D.host.E} (hw : l.Mb ≤ w.asIdeal) (hw' : l.Mb ≤ w'.asIdeal) : ¬ IsConjPl w w' := by
  intro h
  apply w'.isPrime.ne_top
  rw [eq_top_iff, ← l.coprime]
  refine sup_le hw' (Ideal.map_le_iff_le_comap.2 fun a ha => ?_)
  obtain ⟨c', hc', e⟩ := h a (hw ha)
  have : H.bar a = c' := by
    apply RingOfIntegers.coe_injective
    exact (H.bar_eq a).trans e.symm
  show H.bar a ∈ w'.asIdeal
  rw [this]; exact hc'

theorem finR_rfl {D : D7} (V : HSp D) (κ : GA D V) : finR V rfl κ = finE V κ := by
  apply Units.ext
  ext i j
  rfl

theorem exists_isLift : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (l : Level H) (V : HSp D) (r : ℕ) (hr : V.rank = r) (β : GL (Fin r) (EAf D)) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)), IsLatBasis V hr β → (∀ w, w ∈ Pg ↔ l.Mb ≤ w.asIdeal) → ∀ g : Formalism.L2.DIV.G0 Pg r, ∃ κ, IsLift V hr β Pg g κ := by
  intro D H l V r hr β Pg hβ hPg g
  subst hr
  obtain ⟨κ, h1, h2, h3⟩ := GlobalTheory.T.finite_group_lifts_to_parahoric_level V β (datW V.rank Pg (Formalism.L2.DIV.LevelP.triv Pg V.rank ℂ) Frm.B)
    (GlobalTheory.Member.latC V) 1 (isBaseFrame_of_isLatBasis V β hβ) rfl
    (fun w hw w' hw' => not_isConjPl_of_le l ((hPg w).1 hw) ((hPg w').1 hw')) g
  have hs : finR V rfl κ ∈ Formalism.L2.DIV.St β := by
    rw [finR_rfl]; exact Formalism.L2.DIV.parLev_St h2
  refine ⟨κ, h1, hs, fun w => ?_⟩
  have h4 : Formalism.L2.DIV.upperLeftBlock le_rfl (Formalism.L2.DIV.redFn β w.1 (finE V κ)) = g w := congrFun h3 w
  have h5 := Formalism.L2.DIV.upper_block_val_submatrix (r := V.rank) le_rfl
    (Formalism.L2.DIV.blockTri_blkOf_le _ _ (Formalism.L2.DIV.parLev_g h2 w.2))
  rw [h4, ← finR_rfl, Formalism.L2.DIV.redFn, Formalism.L2.DIV.extendOne_of_mem _ hs] at h5
  apply Units.ext
  rw [h5]
  rfl

end GlobalTheory.GeoLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelLiftFiniteCongruence
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts GlobalTheory.GeoLevel
open GlobalTheory.Member (FinCong IotaOK)
open GlobalTheory.LevelCusp (IsMatch)
open GlobalTheory.Dict (castFr)
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftCong

theorem move_mem_of_entries {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (s : A →+* B)
    (hs : Function.Bijective s) (S : Subring B) (β : GL (Fin n) B) (L : AddSubgroup (Fin n → A))
    (hL : ∀ z, z ∈ L ↔ ∀ i, (Units.val (β⁻¹ : GL (Fin n) B)).mulVec (fun a => s (z a)) i ∈ S)
    (k : Matrix (Fin n) (Fin n) A) (y : Matrix (Fin n) (Fin n) S)
    (hk : k.map s = β.val * y.map S.subtype * (β⁻¹ : GL (Fin n) B).val) (c : A) (N : ℕ)
    (hy : ∀ i j, ∃ t ∈ S, s c * (((y - 1 : Matrix (Fin n) (Fin n) S) i j : S) : B) = N * t) :
    ∀ z ∈ L, ∃ w ∈ L, k.mulVec (fun i => c * z i) - (fun i => c * z i) = N • w := by
  classical
  intro z hz
  choose t htS ht using hy
  set x : Fin n → B := (Units.val (β⁻¹ : GL (Fin n) B)).mulVec (fun a => s (z a)) with hx
  have hxS : ∀ i, x i ∈ S := (hL z).1 hz
  obtain ⟨w, hw⟩ : ∃ w : Fin n → A, (fun a => s (w a)) = β.val.mulVec ((Matrix.of t).mulVec x) := by
    choose f hf using hs.2
    exact ⟨fun a => f _, funext fun a => hf _⟩
  refine ⟨w, (hL w).2 fun i => ?_, ?_⟩
  · rw [hw, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    show ∑ j, t i j * x j ∈ S
    exact S.sum_mem fun j _ => S.mul_mem (htS i j) (hxS j)
  · have hz' : (fun a => s (z a)) = β.val.mulVec x := by
      rw [hx, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    have hm : s c • (y.map S.subtype - 1) = (N : B) • Matrix.of t := by
      ext i j
      have := ht i j
      simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply, smul_eq_mul, Matrix.of_apply,
        Subring.coe_subtype]
      rw [← this]
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
    have e1 : (k.map s).mulVec (s c • fun a => s (z a)) - (s c • fun a => s (z a)) =
        (N : B) • fun a => s (w a) := by
      rw [hw, hk, Matrix.mulVec_smul, ← Matrix.mulVec_mulVec, ← hx, hz', ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_smul _ (N : B), ← Matrix.smul_mulVec (N : B), ← hm, Matrix.smul_mulVec, Matrix.sub_mulVec,
        Matrix.one_mulVec, Matrix.mulVec_smul, Matrix.mulVec_sub, smul_sub]
    funext i
    apply hs.1
    have e2 := congrFun e1 i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.map_apply] at e2
    simp only [Pi.sub_apply, Pi.smul_apply, Matrix.mulVec, dotProduct, map_sub, map_sum, map_mul, nsmul_eq_mul,
      map_natCast]
    exact e2

theorem mem_idS_of_resS {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (I : Ideal (𝓞 E)) (h0 : I ≠ ⊥) (hI : I.IsRadical) (s : Formalism.L2.Herm.intAf F E)
    (hs : ∀ w : Formalism.L2.DIV.Pl E, I ≤ w.asIdeal → Formalism.L2.DIV.resS F w s = 0) : s ∈ Formalism.L2.DIV.idS F I := by
  obtain ⟨q, hq⟩ := Formalism.L2.DIV.cmpS_surj (F := F) I h0 (Ideal.Quotient.mk _ s)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hd : Formalism.L2.DIV.oToS F E a - s ∈ Formalism.L2.DIV.idS F I := Ideal.Quotient.eq.1 hq
  have ha : a ∈ I := by
    apply hI
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro J ⟨hJ, hp⟩
    let w : Formalism.L2.DIV.Pl E := ⟨J, hp, fun h => h0 (le_bot_iff.1 (h ▸ hJ))⟩
    have h1 : Formalism.L2.DIV.resS F w (Formalism.L2.DIV.oToS F E a - s) = 0 := by
      have : Formalism.L2.DIV.idS F I ≤ RingHom.ker (Formalism.L2.DIV.resS F w) := by
        refine Ideal.map_le_iff_le_comap.2 fun b hb => ?_
        rw [Ideal.mem_comap, RingHom.mem_ker, Formalism.L2.DIV.resS_oToS]
        exact Ideal.Quotient.eq_zero_iff_mem.2 (hJ hb)
      exact this hd
    rw [map_sub, hs w hJ, sub_zero, Formalism.L2.DIV.resS_oToS] at h1
    exact Ideal.Quotient.eq_zero_iff_mem.1 h1
  have := sub_mem (Ideal.mem_map_of_mem (Formalism.L2.DIV.oToS F E) ha) hd
  rwa [sub_sub_cancel] at this

theorem coe_mul_eq_of_eq {B : Type} [CommRing B] (S : Subring B) (t e c : S) (N : ℕ) (h : t * N = e * c) :
    (c : B) * (e : B) = N * (t : B) := by
  have h4 := congrArg S.subtype h
  rw [map_mul, map_mul, map_natCast] at h4
  rw [mul_comm, mul_comm (N : B)]
  exact h4.symm

theorem swapAE_bijective (D : D7) : Function.Bijective (swapAE D) :=
  (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).bijective

set_option maxHeartbeats 1600000 in
theorem finHom_map_eq {D : D7} (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (κ : GA D V)
    (h : finR V rfl κ ∈ Formalism.L2.DIV.St β) :
    (finHom V κ).1.map (swapAE D) =
      β.val * (Formalism.L2.DIV.pullFr β ⟨finR V rfl κ, h⟩).val.map (OAf D).subtype * (β⁻¹ : GL (Fin V.rank) (EAf D)).val := by
  have h1 := congrArg Units.val (Formalism.L2.DIV.frGL_pullFr β ⟨finR V rfl κ, h⟩)
  exact h1.symm

set_option maxHeartbeats 1600000 in

theorem lift_finCong : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (l : Level H) (V : HSp D) (r : ℕ) (hr : V.rank = r) (β : GL (Fin r) (EAf D)) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)), IsLatBasis V hr β → (∀ w, w ∈ Pg ↔ l.Mb ≤ w.asIdeal) → (∀ (g : Formalism.L2.DIV.G0 Pg r) κ, IsLift V hr β Pg g κ → FinCong V 1 κ) ∧ (l.Mb.IsRadical → ∀ κ, IsLift V hr β Pg 1 κ → FinCong V l.M κ) := by
  intro D H l V r hr β Pg hβ hPg
  subst hr
  refine ⟨fun g κ hκ z hz => ?_, fun hrad κ hκ => ?_⟩
  · obtain ⟨-, h, -⟩ := hκ
    have := move_mem_of_entries (swapAE D) (swapAE_bijective D) (OAf D) β (latHat V) hβ _ _
      (finHom_map_eq V β κ h) 1 1 (fun i j => ⟨_, SetLike.coe_mem ((_ - 1 : Matrix _ _ (OAf D)) i j), by rw [map_one, Nat.cast_one]⟩) z hz
    simp only [one_mul] at this
    exact this
  · obtain ⟨-, h, hw⟩ := hκ
    rw [GlobalTheory.Member.finCong_iff_half D H l V κ]
    intro b hb
    refine move_mem_of_entries (swapAE D) (swapAE_bijective D) (OAf D) β (latHat V) hβ _ _
      (finHom_map_eq V β κ h) ((1 : Af D.host.F) ⊗ₜ (b : D.host.E)) l.M (fun i j => ?_)
    have h0 : l.Mb ≠ ⊥ := by
      intro h0
      have hp := l.prod
      rw [h0, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at hp
      have h3 := l.three_le
      have : l.M = 0 := by exact_mod_cast hp
      omega
    generalize hy : Formalism.L2.DIV.pullFr β ⟨finR V rfl κ, h⟩ = y
    have he : (y.val - 1) i j ∈ Formalism.L2.DIV.idS D.host.F l.Mb := by
      refine mem_idS_of_resS _ h0 hrad _ fun w hle => ?_
      have h1 : Formalism.UG.bc (Formalism.L2.DIV.resS D.host.F w) y = 1 := by
        rw [← hy]; exact hw ⟨w, (hPg w).2 hle⟩
      have h2 : Formalism.L2.DIV.resS D.host.F w (y.val i j) = (1 : Matrix _ _ (Formalism.L2.DIV.kP w)) i j :=
        congrArg (fun g : GL (Fin V.rank) (Formalism.L2.DIV.kP w) => g.val i j) h1
      rw [Matrix.sub_apply, map_sub, h2]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    have hm : (y.val - 1) i j * Formalism.L2.DIV.oToS D.host.F D.host.E b ∈
        Ideal.span {((l.M : ℕ) : OAf D)} := by
      have := Ideal.mul_mem_mul he (Ideal.mem_map_of_mem (Formalism.L2.DIV.oToS D.host.F D.host.E) hb)
      rw [Formalism.L2.DIV.idS, ← Ideal.map_mul, l.prod, Ideal.map_span, Set.image_singleton, map_natCast] at this
      exact this
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hm
    refine ⟨t, t.2, ?_⟩
    exact coe_mul_eq_of_eq _ _ _ _ _ ht

end GlobalTheory.LiftCong
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelSubgroupAdjointScalarStatement
section
open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_subgroup_adjoint_scalar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E L → ∀ (a : GL (Fin n) (AF F ⊗[F] E)) (x : Matrix (Fin n) (Fin 1) E) (pL : Matrix (Fin 1) (Fin n) E), pL * x = 1 → ∀ k ∈ levelAll σ J L a, ∀ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J k).1 * adMat F x = l.1 • adMat F x → absE F E l = 1 := by
  first | exact @GlobalTheory.IwasawaTriv.absE_eigen_eq_one | exact GlobalTheory.IwasawaTriv.absE_eigen_eq_one | (intros; apply GlobalTheory.IwasawaTriv.absE_eigen_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLocalUnitsAlongNilpotentThickeningStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_local_units_along_nilpotent_thickening : ∀ (R : Type) [CommRing R] (J : Ideal R) (X X₀ : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (γ : X₀ ⟶ X) (q : X₀ ⟶ Spec (CommRingCat.of (R ⧸ J))), IsPullback γ q f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) → Surjective γ → ∀ (L : LB X), L.IsLB → ∀ D : X.Opens, IsAffineOpen D → ∀ u : ∀ m : L.ι, Γ(X₀, γ ⁻¹ᵁ (D ⊓ L.U m))ˣ, (∀ z m m', γ z ∈ D ⊓ L.U m → γ z ∈ D ⊓ L.U m' → gm (𝟙 X₀) z _ (u m) = gm γ z _ (L.g m m') * gm (𝟙 X₀) z _ (u m')) → ∃ τ : ∀ m : L.ι, Γ(X, D ⊓ L.U m)ˣ, (∀ m, (γ.app (D ⊓ L.U m)).hom (τ m).val = (u m).val) ∧ ∀ x m m', x ∈ D ⊓ L.U m → x ∈ D ⊓ L.U m' → gm (𝟙 X) x _ (τ m) = gm (𝟙 X) x _ (L.g m m') * gm (𝟙 X) x _ (τ m') := by
  first | exact @GlobalTheory.FormalAlg.lift_localUnits_of_thickening | exact GlobalTheory.FormalAlg.lift_localUnits_of_thickening | (intros; apply GlobalTheory.FormalAlg.lift_localUnits_of_thickening <;> assumption)
end


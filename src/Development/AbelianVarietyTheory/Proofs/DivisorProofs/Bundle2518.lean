import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0328
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0329
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2052
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2042
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2446
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2388
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2284
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2438
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2445
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2419
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2384
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2240
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2407
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1523
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2395
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0020
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0009
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0013
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2420
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2422
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelThetaSeriesSpanOverClassRepresentatives
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound

namespace GlobalTheory.OneKernelSpan

theorem inCoefLat_move : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (Q : Finset (Pl D.host.E)) (h h' : GA D (Vc D i)) (γ : GQ (Vc D i)) (k : Bridge.Gf (Vc D i)), k ∈ dataLevel R i Q → fin (Vc D i) h = Bridge.ratF (Vc D i) γ * fin (Vc D i) h' * k → ∀ w, InCoefLat R i h w → InCoefLat R i h' ((R.cV i).ρ ((γ : GA D (Vc D i))⁻¹) w) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i Q h h' γ k hk e w hw
  obtain ⟨gramR, c0R, c0L, hT, P, hP, rfl⟩ := hw
  refine ⟨gramR, c0R, c0L, hT, ?_⟩
  have hst : Formalism.UG.bc (swapAE D) (k : GL (Fin (Vc D i).rank) _) ∈ St (R.βV i) := Formalism.L2.DIV.parLev_St hk.1
  obtain ⟨γE, hγ, hl⟩ := GlobalTheory.HLatMove.hLat_rat_mul_stab (Vc D i) (R.βV i) (R.ΛV i) (hR.lev.βV i) γ
  rw [e, hl (fin (Vc D i) h') k hst, Formalism.L2.Col.nabAtr_gmap, MulEquiv.apply_symm_apply] at hP
  obtain ⟨P', hP', rfl⟩ := hP
  refine ⟨P', hP', ?_⟩
  have h1 := (hT.mapL i).1 γ γE hγ P'
  change (R.cV i).ρ ((γ : GA D (Vc D i))⁻¹) (c0L i ((rhoVr (labLL D) (lamV D i) γE) P')) = c0L i P'
  rw [h1]
  change ((R.cV i).ρ ((γ : GA D (Vc D i))⁻¹) * (R.cV i).ρ (γ : GA D (Vc D i))) (c0L i P') = c0L i P'
  rw [← map_mul, inv_mul_cancel, map_one]
  rfl

theorem pt_theta_of_kerDat {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} (hR : GlobalTheory.Hk3.Core R F)
    {i : Fin D.R.m} {ξ : Formalism.L2.Host.HChar D.host.E} {χ : (AE D)ˣ →* Circle} {ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ}
    {Q : Finset (Pl D.host.E)} {ω : WeilRep D i} {φ : WO (Vc D i) (Wc D i) → ℂ} (hK : KerDat R i ξ χ ξR Q ω φ)
    (P : PolF D (Wc D i).rank (Vc D i).rank) :
    IsThetaFunO R.ψ (Vc D i) (Wc D i)
      (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) φ P) := by
  have hθ : IsInfFam R.θ := hR.models.inf
  have hφ : IsThetaFunO R.ψ (Vc D i) (Wc D i) φ := by
    obtain ⟨⟨hψ, h0⟩, e, -, h⟩ := hK.vec
    exact GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ hθ h h0.theta
  exact (GlobalTheory.OrientedHeis.om_pureTensorO D _ _ _ _ _ _ _ hK.weil hθ (fun _ => 1) (fun _ => 1) (R.BV i) _
      (cart (R.MW i (sg0 D A))) (cart (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) _ 1 1
      (fun τ => by rw [Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.JointHarm.compAt_mt_one', Matrix.mul_one, Matrix.one_mul]) (fun _ => rfl) (fun _ => rfl) _ hφ P).1

theorem series_rat : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → ∀ γ ∈ GQ (Vc D i), ∀ h w, singleSeries R i ω φ (γ * h) w = singleSeries R i ω φ h w := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i ξ χ ξR Q ω φ hK γ hγ h w
  funext v g
  have := (GlobalTheory.thetaKO_rat_left_and_eigen_right _ _ _ _ _ _ hK.weil _ (pt_theta_of_kerDat hR hK (R.ioP i (PiTensorProduct.tprod ℂ v) w))).1 γ hγ 1 (one_mem _) h g
  rw [one_mul] at this
  exact this

theorem series_level : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → (∀ x, ((ξ.1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → ∀ κ ∈ GfC (Vc D i), fin (Vc D i) κ ∈ dataLevel R i Q → ∃ z : D.what₂.LL, (∃ n : ℕ, 0 < n ∧ z ^ n = 1) ∧ ∀ h w, singleSeries R i ω φ (h * κ) w = D.what₂.embLL z • singleSeries R i ω φ h w := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i ξ χ ξR Q ω φ hK hval κ hκ hk
  obtain ⟨h1, -⟩ := GlobalTheory.T.thetaKernel_vector_moved_by_rootsOfUnity D G Pl0 T0 A Ks R F hR i ξ χ ξR Q ω φ hK hval
  obtain ⟨z, n, hn, hz, hzω⟩ := h1 κ hκ hk
  refine ⟨z, ⟨n, hn, hz⟩, fun h w => ?_⟩
  funext v g
  have hom := GlobalTheory.FiniteFock.om_pureTensorO_of_finite _ _ _ _ _ _ _ hR.models.inf hK.weil _ _ _ _ _
    (pt_theta_of_kerDat hR hK) κ hκ 1 (one_mem _) _ hzω (R.ioP i (PiTensorProduct.tprod ℂ v) w)
  have := (GlobalTheory.thetaKO_rat_left_and_eigen_right _ _ _ _ _ _ hK.weil _ (pt_theta_of_kerDat hR hK (R.ioP i (PiTensorProduct.tprod ℂ v) w))).2 κ 1 _ hom h g
  rw [mul_one] at this
  exact this

theorem series_real : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → ∀ (h u : GA D (Vc D i)), u ∈ GinfC (Vc D i) → ∀ w, singleSeries R i ω φ (h * u) w = singleSeries R i ω φ h ((R.cV i).ρ u w) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i ξ χ ξR Q ω φ hK h u hu w
  funext v g
  unfold singleSeries Datum.thetaKO
  rw [show ((h * u, g) : GA D (Vc D i) × GA D (Wc D i)) = (h, g) * (u, 1) from Prod.ext rfl (mul_one g).symm,
    map_mul, Module.End.mul_apply, GlobalTheory.T.weilAction_kernel_eq_base_on_realUnitaryPoints D G Pl0 T0 A Ks R F hR i ξ χ ξR Q ω φ hK u hu _ (pt_theta_of_kerDat hR hK _),
    GlobalTheory.T.realPoints_act_fock_vectors_any_datum D G Pl0 T0 A Ks R F hR i ξR Q φ hK.vec u hu]

set_option maxHeartbeats 2000000 in

theorem kernelSpanOverClasses_of : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → ∀ (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (ph : ℂ), KernelSpanOverClasses R i U ψ ph v (ownAt D v) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i v hv hmu hval U ψ ph ω φ hk Cl h hh
  obtain ⟨χ, ξR, hK⟩ := GlobalTheory.T.baseTuple_thetaKernel_tameCharacter D G Pl0 T0 A Ks R F hR i v hv hmu ω φ hk
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono (Set.iUnion_subset fun c x hx => ?_))
  · rintro x ⟨g, hg, w, hw, hx⟩
    obtain ⟨c, ⟨γA, hγA⟩, k, e⟩ := hh.2 (fin (Vc D i) g)
    obtain ⟨κ, hκ, hκe⟩ := GlobalTheory.TraceIncl.KernLaws.exists_finite_lift (Vc D i) (k : Bridge.Gf (Vc D i))
    obtain ⟨u, hu_def⟩ : ∃ u : GA D (Vc D i), u = κ⁻¹ * ((h c)⁻¹ * (γA⁻¹ * g)) := ⟨_, rfl⟩
    have e1 : fin (Vc D i) g = fin (Vc D i) (γA * h c * κ) := by
      refine e.trans ?_
      rw [← GlobalTheory.TraceIncl.KernLaws.fin_mul, ← GlobalTheory.TraceIncl.KernLaws.fin_mul, hκe]
      rfl
    have e2 : finHom (Vc D i) g = finHom (Vc D i) (γA * h c * κ) := congrArg Subtype.val e1
    have hu : u ∈ GinfC (Vc D i) := by
      refine MonoidHom.mem_ker.2 ?_
      rw [hu_def, map_mul, map_mul, map_mul, map_inv (finHom (Vc D i)) κ, map_inv (finHom (Vc D i)) (h c),
        map_inv (finHom (Vc D i)) γA, e2, map_mul, map_mul]
      simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel]
    have hg' : g = γA * (h c * κ) * u := by
      rw [hu_def]
      simp only [mul_assoc, mul_inv_cancel_left]
    obtain ⟨z, ⟨n, hn, hz⟩, hzl⟩ := series_level D G Pl0 T0 A Ks R F hR i _ χ ξR _ ω φ hK hval κ hκ (by rw [hκe]; exact k.2)
    have hρ : (R.cV i).ρ u w = (R.cV i).ρ (γA⁻¹) w := by
      have hc1 := (hR.models.cV i).1
      rw [hu_def, map_mul, Module.End.mul_apply, hc1 _ (inv_mem hκ), Module.End.one_apply, map_mul, Module.End.mul_apply,
        hc1 _ (inv_mem (hh.1 c)), Module.End.one_apply, map_mul, Module.End.mul_apply, hc1 _ hg, Module.End.one_apply]
    have key : ∀ v', singleSeries R i ω φ g w v' =
        D.what₂.embLL z • singleSeries R i ω φ (h c) ((R.cV i).ρ (γA⁻¹) w) v' := by
      intro v'
      have h1 := series_real D G Pl0 T0 A Ks R F hR i _ χ ξR _ ω φ hK (γA * (h c * κ)) u hu w
      rw [← hg'] at h1
      have h2 := series_rat D G Pl0 T0 A Ks R F hR i _ χ ξR _ ω φ hK γA hγA (h c * κ) ((R.cV i).ρ u w)
      have h3 := hzl (h c) ((R.cV i).ρ u w)
      rw [h1, h2, h3, hρ]
      rfl
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hn.ne'] at hz
      exact zero_ne_one hz
    have hzI : IsIntegral ℤ z := IsIntegral.of_pow hn (by rw [hz]; exact isIntegral_one)
    have hx'' : z⁻¹ • x ∈ seriesAt R i U ψ ph ω φ (h c) := by
      refine ⟨_, inCoefLat_move D G Pl0 T0 A Ks R F hR i _ g (h c) ⟨γA, hγA⟩ k k.2 e w hw, fun v' => ?_⟩
      rw [adForm_smul]
      change D.what₂.embLL z⁻¹ • adForm R i x (fun ρ => v' ρ) = _
      rw [hx v', key v', map_smul, smul_comm ph, smul_smul, ← map_mul, inv_mul_cancel₀ hz0, map_one, one_smul]
    have : x = (⟨z, hzI⟩ : 𝓞 D.what₂.LL) • (z⁻¹ • x) := by
      have e3 : (⟨z, hzI⟩ : 𝓞 D.what₂.LL) • (z⁻¹ • x) = z • (z⁻¹ • x) := rfl
      rw [e3, smul_smul, mul_inv_cancel₀ hz0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_iUnion.2 ⟨c, hx''⟩))
  · obtain ⟨w, hw, hx⟩ := hx
    exact ⟨h c, hh.1 c, w, hw, hx⟩

end GlobalTheory.OneKernelSpan

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyDatumPullbackBaseChangeLieBasis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyEvenBC

theorem keyOn_pullback : ∀ (A B K : Type) [CommRing A] [CommRing B] [CommRing K] (f : A →+* B) (h : B →+* K) (G : Over (Sp A)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ : L.L.Sec) (x : KeyIn K) (y : Fin x.P.g → (epsR A ⟶ G)), IsSemiAbelian G → IsLieBasis y → NzFib σ → KeyOn (h.comp f) x G L σ y → ∀ [IsCommMonObj ((Over.pullback (spMap f)).obj G)], ∃ (L' : RigLB ((Over.pullback (spMap f)).obj G)) (σ' : L'.L.Sec) (y' : Fin x.P.g → (epsR B ⟶ (Over.pullback (spMap f)).obj G)), LBIso (L.L.pull (pullback.fst G.hom (spMap f))) L'.L ∧ IsLieBasis y' ∧ NzFib σ' ∧ KeyOn h x ((Over.pullback (spMap f)).obj G) L' σ' y' := by
  intro A B K _ _ _ f h G _ _ L σ x y hG hy hσ hK _
  obtain ⟨φ, he, ψ, F, hφ, hψ, hrig, hsec, hF1, hF2, hFv⟩ := hK
  have hP := isGrpPullback_pullback G (spMap f)
  have sqφ : φ ≫ G.hom = (x.P.A.hom ≫ spMap h) ≫ spMap f := by
    rw [Category.assoc, ← spMap_comp]
    exact hφ.1.w
  obtain ⟨φ', hφ', hfst, hsnd⟩ : ∃ φ' : x.P.A.left ⟶ ((Over.pullback (spMap f)).obj G).left,
      IsGrpPullback x.P.A ((Over.pullback (spMap f)).obj G) (spMap h) φ' ∧ φ' ≫ pullback.fst G.hom (spMap f) = φ ∧
        φ' ≫ ((Over.pullback (spMap f)).obj G).hom = x.P.A.hom ≫ spMap h := by
    refine ⟨pullback.lift φ (x.P.A.hom ≫ spMap h) sqφ, ?_, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    refine IsGrpPullback.cancel hP ?_ (pullback.lift_snd _ _ _)
    rw [pullback.lift_fst, ← spMap_comp]
    exact hφ
  subst hfst
  have hL := L.isLB
  have hL' : (L.L.pull (pullback.fst G.hom (spMap f))).IsLB := LB.isLB_pull hL _
  have heF : eSec ((Over.pullback (spMap f)).obj G) ≫ pullback.fst G.hom (spMap f) = spMap f ≫ eSec G :=
    PolBaseChange.eSec_comm hP
  let L' : RigLB ((Over.pullback (spMap f)).obj G) :=
    ⟨L.L.pull (pullback.fst G.hom (spMap f)), rigPullOf (G' := ((Over.pullback (spMap f)).obj G)) (pullback.fst G.hom (spMap f)) (spMap f) heF L.L L.rig, hL',
      Out.LBxP.isGen_pullAlong L.L (pullback.fst G.hom (spMap f)) (spMap f) (fun _ : PUnit => eSec G) (fun _ => 1)
        (fun _ => eSec ((Over.pullback (spMap f)).obj G)) (fun _ => heF) L.rig L.rigGen⟩
  have he' : eSec x.P.A ≫ φ' = spMap h ≫ eSec ((Over.pullback (spMap f)).obj G) := PolBaseChange.eSec_comm hφ'
  have pw := (isGen_iff (L := L.L) (F := pullback.fst G.hom (spMap f)) (idIso _)).1 (idIso_isGen hL')
  obtain ⟨σ', hσ'⟩ := sec_pull_down pw hL hL' σ
  have pψ := (isGen_iff ψ).1 hψ
  obtain ⟨w', T⟩ := exists_cancel hL (idIso (L.L.pull (pullback.fst G.hom (spMap f)))) ψ pw pψ hL' x.P.isLB
  have H : PMaps (idIso (L.L.pull (pullback.fst G.hom (spMap f)))) (K := PUnit)
      (fun _ => eSec ((Over.pullback (spMap f)).obj G)) (fun _ => eSec G) (fun _ => 1) L'.rig L.rig (spMap f) :=
    (maps_iff _ _ _ _ L'.rig L.rig (spMap f) L'.rig (rigPull_le (G' := ((Over.pullback (spMap f)).obj G)) (pullback.fst G.hom (spMap f)) (spMap f) heF L.L) (fun _ => rfl)).1 (idIso_maps L')
  have H'' : PMaps ψ (K := PUnit) (fun _ => eSec x.P.A) (fun _ => eSec G) (fun _ => 1) x.rig L.rig
      (spMap h ≫ spMap f) := by
    rw [← spMap_comp]
    exact (maps_iff ψ _ _ _ x.rig L.rig (spMap (h.comp f)) _ (rigPull_le (G' := x.P.A) (φ' ≫ pullback.fst G.hom (spMap f)) (spMap (h.comp f)) he L.L)
      (fun _ => rfl)).1 hrig
  have H' := T.pmaps_cancel hL (fun _ => he') H H''
  have hrig' : LB.Gen.Maps (LB.linCombIso w' (K := PUnit) (fun _ => eSec x.P.A) (fun _ => 1)) x.rig
      (rigPullOf φ' (spMap h) he' L'.L L'.rig) :=
    (maps_iff w' _ _ _ x.rig L'.rig (spMap h) _ (rigPull_le φ' (spMap h) he' L'.L) (fun _ => rfl)).2 H'

  have hsec' : ∀ (j : (L'.L.pull φ').ι) (i : x.P.L.ι) (hh : (L'.L.pull φ').U j ⊓ x.P.L.U i ≤ φ' ⁻¹ᵁ L'.L.U (j PUnit.unit)),
      (φ'.appLE _ _ hh).hom (σ'.f (j PUnit.unit)) =
        (show Γ(x.P.A.left, (L'.L.pull φ').U j ⊓ x.P.L.U i) from (w'.s (j, i)).val) * resG _ inf_le_right (x.th.f i) := by
    refine GlobalTheory.KeyPow.appLE_eq_of_stalk w' σ' x.th ?_
    intro z J k hJ hk
    have ha : (pullback.fst G.hom (spMap f)) (φ' z) ∈ L.L.U (J PUnit.unit) := mem_pull.1 hJ
    have hW : (𝟙 x.P.A.left) z ∈ (L.L.pull (φ' ≫ pullback.fst G.hom (spMap f))).U (fun _ => J PUnit.unit) ⊓ x.P.L.U k :=
      ⟨mem_pull.2 ha, hk⟩
    have s2 : gs (𝟙 _ ≫ φ' ≫ pullback.fst G.hom (spMap f)) z _ (σ.f (J PUnit.unit)) =
        (gw ψ (𝟙 _) z (J PUnit.unit) k).val * gs (𝟙 _) z _ (x.th.f k) := by
      have e := congrArg (gs (𝟙 _) z ((L.L.pull (φ' ≫ pullback.fst G.hom (spMap f))).U (fun _ => J PUnit.unit) ⊓ x.P.L.U k))
        (hsec (fun _ => J PUnit.unit) k (fun x hx => mem_pull.1 hx.1))
      exact (gs_appLE (φ' ≫ pullback.fst G.hom (spMap f)) _ _ _ (𝟙 _) z hW _).symm.trans (e.trans ((gs_mul _ z _ hW _ _).trans
        (congrArg₂ (· * ·) (gs_unit _ z _ hW _) (gs_res _ z _ hW _))))
    have e1 := hσ' _ (𝟙 _ ≫ φ') z (J PUnit.unit) J ha hJ
    have e3 := T _ (𝟙 _) z (J PUnit.unit) J k ha hJ hk
    rw [Category.assoc] at e1
    rw [e1, e3, Units.val_mul, _root_.mul_assoc] at s2
    exact (Units.mul_right_inj _).1 s2
  have hnz : NzFib (L := L'.L) σ' := by
    intro s
    obtain ⟨z, hz, hz'⟩ := hσ (spMap f s)
    obtain ⟨y0, rfl, hy0⟩ := Scheme.exists_preimage_of_isPullback hP.1 z s hz
    obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hz'
    refine ⟨y0, hy0, (mem_nonzeroLocus _ _).2 ⟨fun _ => k, mem_pull.2 hk, ?_⟩⟩
    have u₁ : IsUnit (gs (pullback.fst G.hom (spMap f)) y0 _ (σ.f k)) := by
      rw [gs_stalkMap _ y0 _ hk]; exact u.map _
    have e := hσ' _ (𝟙 _) y0 k (fun _ => k) hk (mem_pull.2 hk)
    rw [Category.id_comp] at e
    exact isUnit_of_mul_isUnit_right (e ▸ u₁)

  have := hG.smooth
  have sq : ∀ i, (spMap (Chart.dualMapR f) ≫ (y i).left) ≫ G.hom = (epsR B).hom ≫ spMap f := fun i => by
    rw [Category.assoc, Over.w]
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  let y' : Fin x.P.g → (epsR B ⟶ ((Over.pullback (spMap f)).obj G)) := fun i =>
    Over.homMk (hP.1.lift _ _ (sq i)) (hP.1.lift_snd _ _ _)
  have hy' : ∀ i, (y' i).left ≫ pullback.fst G.hom (spMap f) = spMap (Chart.dualMapR f) ≫ (y i).left :=
    fun i => hP.1.lift_fst _ _ _
  have hadd : ∀ (a b : B) (w : Chart.sp (DualNumber B) ⟶ ((Over.pullback (spMap f)).obj G)), Chart.IsTan w →
      Chart.spMap (Chart.scaleD (a + b)) ≫ w = (Chart.spMap (Chart.scaleD a) ≫ w) * (Chart.spMap (Chart.scaleD b) ≫ w) :=
    fun a b w hw => GlobalTheory.LieMultiple.scale_add ((Chart.isTan_iff w).1 hw) a b
  have hT : ∀ i, IsTangent (y' i) := fun i => by
    refine hP.1.hom_ext ?_ ?_
    · rw [Category.assoc, hy', show η[((Over.pullback (spMap f)).obj G)].left = eSec ((Over.pullback (spMap f)).obj G) from rfl, heF, ← Category.assoc]
      have e0 := hy.1 i
      rw [IsTangent] at e0
      rw [show eSec G = η[G].left from rfl, ← e0, ← Category.assoc]
      congr 1
      show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      refine RingHom.ext fun a => ?_
      simp [Chart.dualMapR]
    · rw [Category.assoc, Over.w (y' i), Over.w η[((Over.pullback (spMap f)).obj G)]]
      show Spec.map _ ≫ Spec.map _ = 𝟙 _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      convert Spec.map_id (CommRingCat.of B)
      ext a; simp
  have hLie : IsLieBasis y' := Chart.frameLieBCR G hy f hP hadd hT hy'

  have hF' : F = (Chart.dualMapR h).comp (Chart.dualMapR f) := by
    refine GlobalTheory.KeyExtLie.dnRingHom_ext (fun a => ?_) ?_
    · have e1 := hF1 a
      simp only [TrivSqZeroExt.algebraMap_eq_inl] at e1
      rw [e1]
      simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
    · rw [hF2]
      ext <;> simp [Chart.dualMapR]
  have hv' : ∀ i, (x.v i).left ≫ φ' = spMap (Chart.dualMapR h) ≫ (y' i).left := fun i => by
    refine hP.1.hom_ext ?_ ?_
    · rw [Category.assoc, hFv i, Category.assoc, hy', ← Category.assoc, hF', spMap_comp]
    · rw [Category.assoc, hsnd, ← Category.assoc, Over.w (x.v i), Category.assoc, Over.w (y' i)]
      show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  refine ⟨L', σ', y', ⟨idIso _, idIso_isGen hL'⟩, hLie, hnz, φ', he', w', Chart.dualMapR h, hφ',
    (isGen_iff w').2 (T.pgen_cancel hL pw pψ), hrig', hsec', fun a => ?_, ?_, hv'⟩
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]

end GlobalTheory.KeyEvenBC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerChangeOfTangentFrame
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

open MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.KSFrameChange

theorem sum_four_comm {R : Type} [AddCommMonoid R] {ι₁ ι₂ ι₃ ι₄ : Type} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    [Fintype ι₄] (F : ι₁ → ι₂ → ι₃ → ι₄ → R) :
    ∑ a, ∑ b, ∑ x, ∑ y, F a b x y = ∑ y, ∑ x, ∑ b, ∑ a, F a b x y :=
  calc ∑ a, ∑ b, ∑ x, ∑ y, F a b x y = ∑ a, ∑ b, ∑ y, ∑ x, F a b x y :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a, ∑ y, ∑ b, ∑ x, F a b x y := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ y, ∑ a, ∑ b, ∑ x, F a b x y := Finset.sum_comm
    _ = ∑ y, ∑ a, ∑ x, ∑ b, F a b x y :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ y, ∑ x, ∑ a, ∑ b, F a b x y := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ y, ∑ x, ∑ b, ∑ a, F a b x y :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem sum_four_comm' {R : Type} [AddCommMonoid R] {ι₁ ι₂ ι₃ ι₄ : Type} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    [Fintype ι₄] (F : ι₁ → ι₂ → ι₃ → ι₄ → R) :
    ∑ a, ∑ b, ∑ x, ∑ y, F a b x y = ∑ x, ∑ y, ∑ b, ∑ a, F a b x y :=
  (sum_four_comm F).trans Finset.sum_comm

theorem isKS_frame_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X)
    (V : X.Opens) (U : X.affineOpens) (n n' : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left))
    (v' : Fin n' → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (B : Matrix (Fin n) (Fin n') Γ(X, U.1))
    (D : Γ(X, U.1) → Γ(X, U.1)) (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)),
    (∀ a, IsTanAtG t (GlobalTheory.LogKS.chart U) (v a)) → (∀ c, IsTanAtG t (GlobalTheory.LogKS.chart U) (v' c)) →
    (∀ a, IsCombAtG t (GlobalTheory.LogKS.chart U) v' (B a) (v a)) → GlobalTheory.LogKS.IsKS t V U v D Θ →
    GlobalTheory.LogKS.IsKS t V U v' D (_root_.Matrix.transpose B * Θ * B) := by
  intro E _ _ _ H X t V U n n' v v' B D Θ hv hv' hB hKS
  obtain ⟨J, W, j, d, hcov, hWL, hF, hD, hc⟩ := hKS
  refine ⟨J, W, j, d, hcov, hWL, hF, hD, ?_⟩
  intro i i' O hO f S _ φ g₀ w' hg hgO htr'
  choose w hw using fun a => (GlobalTheory.LogKS.existsUnique_isTranslate t φ hg (hv a)).exists
  rw [hc i i' O hO f S φ g₀ w hg hgO hw]
  let g' : overAt (g₀ ≫ t.G.hom) (DualNumber S) ⟶ t.G :=
    Over.homMk (spMap (algebraMap S (DualNumber S)) ≫ g₀) (Category.assoc _ _ _)
  choose gc yc hgc hyc hwc using htr'
  have hgc' : ∀ c, gc c = g' := fun c => Over.OverMorphism.ext (hgc c)
  have key : ∀ a (O' : t.G.left.Opens) (f' : Γ(t.G.left, O')), ⊤ ≤ g₀ ⁻¹ᵁ O' →
      (valR (w a) O' f').snd = ∑ c, φ (B a c) * (valR (w' c) O' f').snd := by
    intro a O' f' hO'
    obtain ⟨h0, hw'⟩ := GlobalTheory.T.translate_tangent_combination_eq_prod t U v' (B a) (v a) φ g₀ hg g' yc hv' (hB a) rfl hyc
    rw [hw' (w a) (hw a), GlobalTheory.T.snd_sectionValue_translate_prod_first_order_linear (g₀ ≫ t.G.hom) t.G g₀ g' rfl yc (fun c => φ (B a c)) h0 O' f' hO']
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← hwc c, hgc' c]
  simp_rw [key _ O f hgO]
  have hO2 : ⊤ ≤ g₀ ⁻¹ᵁ (t.PP.L.U (j i) ⊓ t.PP.L.U (j i')) :=
    hgO.trans (fun x hx => (hO.trans (inf_le_inf (hWL i) (hWL i'))) hx)
  simp_rw [key _ _ _ hO2]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [sum_four_comm']
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.KSFrameChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerRowOfKodairaSpencerValueHodgeFilStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodairaSpencerRow_of_kodairaSpencerValue_hodgeFil : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i), IsAbelianScheme A → ∀ (ψ : LinearMap.BilinForm K (GlobalTheory.DeRham.HdR A)) (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR K ⟶ A)) (hb : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → GlobalTheory.DeRham.HdR A) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (θ : Matrix (Fin n) (Fin n) K) (s : K), (∀ σ k, IsTangent (ub σ k)) → (∀ a b, (e.symm a).1 ≠ conjEmb (e.symm b).1 → θ a b = 0) → (∀ f ∈ GlobalTheory.DeRham.Fil A, ∀ w, IsLieComb (fun a => s * ∑ b, θ a b * ψ f (hb (e.symm b))) (fun a => ub (e.symm a).1 (e.symm a).2) w → GlobalTheory.DeRham.IsKSValue h f w) → ∀ (τ : E →+* ℂ) (a₀ : Fin (Dw.mult (conjEmb τ))), (∃ w, GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨conjEmb τ, a₀⟩ w) → ∃ w, IsLieComb (fun b => s * θ (e ⟨τ, b⟩) (e ⟨conjEmb τ, a₀⟩)) (ub τ) w ∧ GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨conjEmb τ, a₀⟩ w := by
  first | exact @GlobalTheory.KSRowsFil.isKSRow_of_isKSValue | exact GlobalTheory.KSRowsFil.isKSRow_of_isKSValue | (intros; apply GlobalTheory.KSRowsFil.isKSRow_of_isKSValue <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerZeroTangentTrivial
section
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.FlagTan

theorem eq_const_of_isKS_zero : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
      (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K)
      (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → IsTanX y x' → IsKS (psiSet H) y x' 0 →
        x' = spMap (algebraMap K (DualNumber K)) ≫ y.x := by
  intro P G E _ _ _ H Dw l Xo c K _ _ y x' hpq hx hks
  obtain ⟨A, _, A', _, π, π', i, h, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_group_lift_kodaira_spencer_zero P E H Dw l Xo c K y x' hpq hx hks
  obtain ⟨q, hq1, hq2⟩ := GlobalTheory.T.group_lift_tangent_compatibility P G E H Dw l Xo c K y x' hpq hx A A' π π' i h h1 h2 h3 h4
  obtain ⟨o, m⟩ := GlobalTheory.obj_pull E H Dw l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ Xo.s (x' ≫ Xo.s) x' rfl rfl
    (by rw [spMap, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]) Xo.univ
  have e := Xo.unram K x' o m
    (GlobalTheory.T.group_lift_tangent_uniqueness P G E H Dw l Xo c K y x' hpq hx A A' π π' i q h h1 h2 h3 hq1 hq2 o m)
  rw [← hx.2]
  conv_lhs => rw [e]
  rfl

end GlobalTheory.FlagTan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePreservingMapGivesEndomorphism
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult.Obj

theorem holUnif_dim_eq_of_linear {A : Over (Sp ℂ)} [GrpObj A] {L L' : LB A.left} {g g' : ℕ} (u : HolUnif A L g)
    (u' : HolUnif A L' g') (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hF : ∀ z, u'.ex (F z) = u.ex z) : g = g' := by
  haveI := u.discrete
  haveI := u'.discrete
  have hinj := AnyUnif.injective_of_ker_le_discrete u.Λ F fun z hz => by
    rw [← u.ker, ← hF, hz]
    exact (u'.ker 0).2 u'.Λ.zero_mem
  have hsurj : LinearMap.range F = ⊤ := GlobalTheory.AHWeil.eq_top_of_add_discrete u'.Λ _ fun w => by
    obtain ⟨z, hz⟩ := u.ex_onto (u'.ex w)
    refine ⟨⟨w - F z, (u'.ker _).1 ?_⟩, z, by simp⟩
    have h := u'.ex_add (w - F z) (F z)
    rw [sub_add_cancel, hF, hz] at h
    exact (mul_eq_right.1 h.symm)
  simpa using (LinearEquiv.ofBijective F ⟨hinj, LinearMap.range_eq_top.1 hsurj⟩).finrank_eq

theorem holUnif_dim_eq {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} (X : Obj F 𝔠 (Sp ℂ))
    {M : LB X.A.left} {g : ℕ} (u : HolUnif X.A M g) : g = Module.finrank ℚ F := by
  obtain ⟨L₀, u₀, -, -⟩ := Obj.exists_holUnif_ringHom_lift F 𝔠 X
  obtain ⟨h₁, h₂⟩ := TorusTransfer.tangent_bijective u₀ X.dim
  obtain ⟨T, hT, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo X.A X.ab L₀ (Module.finrank ℚ F) g u₀ h₁ h₂
    u.ex u.ex_add (fun U f => by simpa only [Set.mem_univ, true_and] using u.hol U f)
  exact holUnif_dim_eq_of_linear u u₀ T hT

theorem exists_isMonHom_of_map_lattice : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X : Obj F 𝔠 (Sp ℂ)) (M : LB X.A.left) (g : ℕ)
    (u : HolUnif X.A M g) (T : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ w ∈ u.Λ, T w ∈ u.Λ) →
      ∃ α : X.A ⟶ X.A, IsMonHom α ∧ ∀ w, u.ex (T w) = u.ex w ≫ α := by
  intro F _ _ 𝔠 X M g u T hT
  have hg := holUnif_dim_eq X u
  subst hg
  exact GlobalTheory.HolUnifEnd.exists_isMonHom_of_map_lattice X.A _ X.ab X.dim M u T hT

end GlobalTheory.RealMult.Obj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructurePullbackExistsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_structure_pullback_exists : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S S' : Scheme.{0}} {X : Obj F 𝔠 S} {X' : Obj F 𝔠 S'} {b : S' ⟶ S}
    {φ : X'.A.left ⟶ X.A.left}, X'.IsPullBy X b φ → ∀ {N : ℕ} (α : X.Level N),
    ∃ α' : X'.Level N, ∀ i, (α'.pt i).left ≫ φ = b ≫ (α.pt i).left := by
  first | exact @GlobalTheory.RealMult.LevelPull.exists_level_pull | exact GlobalTheory.RealMult.LevelPull.exists_level_pull | (intros; apply GlobalTheory.RealMult.LevelPull.exists_level_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalEquationMemComapMapIdealSheafNearPointStatement
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localEquation_mem_comap_map_idealSheaf_near_point : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M₁ M : RatModel o Ω) (π : M.Z ⟶ M₁.Z), M₁.IsHom M (AlgHom.id o Ω) π → ∀ (D : EffCartierData M.Z) (V : M₁.Z.affineOpens) (g : Γ(M₁.Z, V.1)) (x : M.Z) (i : D.ι), π x ∈ V.1 → x ∈ D.U i → g ∈ (D.idealSheaf.map π).ideal V → valF M₁.pt V.1 g ≠ 0 → valF M.pt (D.U i) (D.f i) / valF M₁.pt V.1 g ∈ M.O x → ∃ (W : M.Z.affineOpens) (h : W.1 ≤ D.U i), x ∈ W.1 ∧ resG M.Z h (D.f i) ∈ ((D.idealSheaf.map π).comap π).ideal W := by
  first | exact @GlobalTheory.Poinc.resG_f_mem_comap_map_ideal | exact GlobalTheory.Poinc.resG_f_mem_comap_map_ideal | (intros; apply GlobalTheory.Poinc.resG_f_mem_comap_map_ideal <;> assumption)
end


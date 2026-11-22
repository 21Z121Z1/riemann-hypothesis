import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2413
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSymmetricSqrtPrincipalSiegelFiniteEtale
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1600
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2389
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0638
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2402
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHom
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Poinc.GalAut

section General

variable {o Ω₁ Ω₂ : Type} [CommRing o] [Field Ω₁] [Algebra o Ω₁] [Field Ω₂] [Algebra o Ω₂]
  {M₁ : RatModel o Ω₁} {N : RatModel o Ω₂} {φ : Ω₁ →ₐ[o] Ω₂} {q : N.Z ⟶ M₁.Z} [IsFinite q]

theorem map_ringOn (hf : M₁.IsHom N φ q) (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme N.Z) (τ : Ω₂ →ₐ[o] Ω₂) (hτ : ∀ a, τ (φ a) = φ a)
    {U₀ : M₁.Z.Opens} (hU₀ : IsAffineOpen U₀) (hne : ((q ⁻¹ᵁ U₀ : N.Z.Opens) : Set N.Z).Nonempty) :
    ∀ x ∈ N.ringOn ((q ⁻¹ᵁ U₀ : N.Z.Opens) : Set N.Z), τ x ∈ N.ringOn ((q ⁻¹ᵁ U₀ : N.Z.Opens) : Set N.Z) := by
  intro x hx
  obtain ⟨f, rfl⟩ := (RatModel.mem_ringOn_iff_exists hne).1 hx
  refine RatModel.mem_ringOn.2 fun z hz => ?_
  have hzU : q z ∈ U₀ := hz
  haveI := RatModel.isIntegrallyClosed_O hn z
  letI : Algebra Γ(M₁.Z, U₀) Γ(N.Z, q ⁻¹ᵁ U₀) := (q.app U₀).hom.toAlgebra
  have hi : IsIntegral Γ(M₁.Z, U₀) f := (IsFinite.finite_app q U₀ hU₀).to_isIntegral f
  have hmem : ∀ a : Γ(M₁.Z, U₀), φ.toRingHom (M₁.res U₀ ⟨_, hzU⟩ a) ∈ N.O z := fun a => by
    have e : φ.toRingHom (M₁.res U₀ ⟨_, hzU⟩ a) = φ (valF M₁.pt U₀ a) := congrArg φ (M₁.res_apply _ _ a)
    rw [e]
    exact hf.map_mem_O (z := z) (RatModel.valF_mem_O hzU a)
  let χ : Γ(M₁.Z, U₀) →+* N.O z :=
    RingHom.codRestrict (φ.toRingHom.comp (M₁.res U₀ ⟨_, hzU⟩)) (N.O z) hmem
  let ψ : Γ(N.Z, q ⁻¹ᵁ U₀) →+* Ω₂ := τ.toRingHom.comp (N.res (q ⁻¹ᵁ U₀) hne)
  have hc : (algebraMap (N.O z) Ω₂).comp χ = ψ.comp (algebraMap Γ(M₁.Z, U₀) Γ(N.Z, q ⁻¹ᵁ U₀)) := by
    ext a
    have e := hf.valF_app ⟨_, hzU⟩ a
    change φ (M₁.res U₀ ⟨_, hzU⟩ a) = τ (N.res (q ⁻¹ᵁ U₀) hne ((q.app U₀).hom a))
    calc φ (M₁.res U₀ ⟨_, hzU⟩ a) = φ (valF M₁.pt U₀ a) := congrArg φ (M₁.res_apply _ _ a)
      _ = τ (φ (valF M₁.pt U₀ a)) := (hτ _).symm
      _ = τ (valF N.pt (q ⁻¹ᵁ U₀) (q.app U₀ a)) := congrArg τ e.symm
      _ = τ (N.res (q ⁻¹ᵁ U₀) hne ((q.app U₀).hom a)) := congrArg τ (N.res_apply _ _ _).symm
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.1 (hi.map_of_comp_eq χ ψ hc)
  have e2 : ψ f = τ (valF N.pt (q ⁻¹ᵁ U₀) f) := congrArg τ (N.res_apply _ _ f)
  have e3 : τ (valF N.pt (q ⁻¹ᵁ U₀) f) = (w : Ω₂) := e2.symm.trans hw.symm
  rw [e3]
  exact w.2

theorem exists_isHom (hf : M₁.IsHom N φ q) (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme N.Z) (τ : Ω₂ →ₐ[o] Ω₂)
    (hτ : ∀ a, τ (φ a) = φ a) : ∃ s : N.Z ⟶ N.Z, N.IsHom N τ s := by
  refine RatModel.exists_isHom_of_local fun z => ?_
  obtain ⟨U₀, hU₀, hz, -⟩ := exists_isAffineOpen_mem_and_subset (U := (⊤ : M₁.Z.Opens)) (x := q z) trivial
  exact ⟨q ⁻¹ᵁ U₀, q ⁻¹ᵁ U₀, hz, hU₀.preimage q, ⟨z, hz⟩, map_ringOn hf hn τ hτ hU₀ ⟨z, hz⟩⟩

end General

section Over

variable {o₁ Ω₁ o₂ Ω₂ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂]
  [Algebra o₂ Ω₂] [Algebra Ω₁ Ω₂] [Algebra o₁ Ω₂]

def overBase (M₁ : RatModel o₁ Ω₁) (M₂ : RatModel o₂ Ω₂) (q : M₂.Z ⟶ M₁.Z) [IsFinite q]
    (hq : M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt)
    (hA : algebraMap o₁ Ω₂ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁)) : RatModel o₁ Ω₂ where
  Z := M₂.Z
  s := q ≫ M₁.s
  sep := by haveI := M₁.sep; infer_instance
  lft := by haveI := M₁.lft; infer_instance
  qc := by haveI := M₁.qc; infer_instance
  pt := M₂.pt
  pt_s := by
    rw [← Category.assoc, hq, Category.assoc, M₁.pt_s, hA]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  gen := M₂.gen
  onto := M₂.onto

def incl (hA : algebraMap o₁ Ω₂ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁)) : Ω₁ →ₐ[o₁] Ω₂ :=
  { algebraMap Ω₁ Ω₂ with commutes' := fun r => by rw [hA]; rfl }

theorem autO_comm (hA : algebraMap o₁ Ω₂ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁)) (σ : Ω₂ ≃ₐ[Ω₁] Ω₂)
    (r : o₁) : σ (algebraMap o₁ Ω₂ r) = algebraMap o₁ Ω₂ r := by
  rw [hA]
  exact σ.commutes (algebraMap o₁ Ω₁ r)

def autO (hA : algebraMap o₁ Ω₂ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁)) (σ : Ω₂ ≃ₐ[Ω₁] Ω₂) :
    Ω₂ →ₐ[o₁] Ω₂ :=
  { (σ : Ω₂ →+* Ω₂) with commutes' := fun r => autO_comm hA σ r }

theorem autO_apply (hA : algebraMap o₁ Ω₂ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁)) (σ : Ω₂ ≃ₐ[Ω₁] Ω₂)
    (x : Ω₂) : autO hA σ x = σ x := rfl

end Over

theorem autAct : ∀ (o₁ Ω₁ o₂ Ω₂ : Type) [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [Algebra Ω₁ Ω₂] (M₁ : RatModel o₁ Ω₁) (M₂ : RatModel o₂ Ω₂) (q : M₂.Z ⟶ M₁.Z), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₂.Z → IsFinite q → M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt → ∀ σ : Ω₂ ≃ₐ[Ω₁] Ω₂, ∃ s : M₂.Z ⟶ M₂.Z, M₂.pt ≫ s = spMap (σ : Ω₂ →+* Ω₂) ≫ M₂.pt ∧ s ≫ q = q ∧ ∀ (K : Type) [Field K] (y : Sp K ⟶ M₂.Z) (b : Ω₂), M₂.val (y ≫ s) b = M₂.val y (σ b) := by
  intro o₁ Ω₁ o₂ Ω₂ _ _ _ _ _ _ _ M₁ M₂ q hn hfin hq σ
  haveI := hfin
  letI : Algebra o₁ Ω₂ := ((algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁)).toAlgebra
  have hA : algebraMap o₁ Ω₂ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁) := rfl
  let N := overBase M₁ M₂ q hq hA
  haveI hfN : IsFinite (show N.Z ⟶ M₁.Z from q) := hfin
  have hqN : M₁.IsHom N (incl hA) q := hq
  have hnN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme N.Z := hn
  obtain ⟨s, hs⟩ := exists_isHom hqN hnN (autO hA σ) fun a => σ.commutes a
  obtain ⟨t, ht⟩ := exists_isHom hqN hnN (autO hA σ.symm) fun a => σ.symm.commutes a
  have hst : s ≫ t = 𝟙 N.Z := by
    have h1 := ht.comp hs
    have e : (autO hA σ).comp (autO hA σ.symm) = AlgHom.id o₁ Ω₂ := by
      ext x
      exact σ.apply_symm_apply x
    rw [e] at h1
    exact h1.unique (RatModel.isHom_id N)
  have hsq : s ≫ q = q := by
    have h1 := hqN.comp hs
    have e : (autO hA σ).comp (incl hA) = incl hA := by
      ext a
      exact σ.commutes a
    rw [e] at h1
    exact h1.unique hqN
  refine ⟨s, hs, hsq, fun K _ y b => ?_⟩
  let w : Sp K := IsLocalRing.closedPoint K
  have hts : ∀ z, t (s z) = z := fun z => by
    rw [← Scheme.Hom.comp_apply, hst]
    rfl
  by_cases hb : b ∈ N.O (s (y w))
  · exact hs.val_comp y w hb
  · have hb' : σ b ∉ N.O (y w) := by
      intro h
      apply hb
      have h2 := ht.map_mem_O (z := s (y w)) (x := σ b) (by
        have e : N.O (t (s (y w))) = N.O (y w) := congrArg N.O (hts (y w))
        rw [e]; exact h)
      simpa [autO_apply] using h2
    have e1 : M₂.val (y ≫ s) b = 0 := RatModel.val_of_notMem (M := N) (y := y ≫ s) w hb
    have e2 : M₂.val y (σ b) = 0 := RatModel.val_of_notMem (M := N) (y := y) w hb'
    rw [e1, e2]

end GlobalTheory.Poinc.GalAut
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoCancelPulledBundlesGerms
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.IsoComp

theorem pullIsoAlong {Y XA XG : Scheme.{0}} (θ : Y ⟶ XA) (φ : XA ⟶ XG) (G : Y ⟶ XG) (hG : θ ≫ φ = G)
    {LP : LB XA} {LL : LB XG} (ψ : LB.Iso LP (LL.pull φ)) (hψ : PGen ψ) :
    ∃ w : LB.Iso (LP.pull θ) (LL.pull G), PGen w ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : LL.ι) (K : PUnit → LP.ι), G (r z) ∈ LL.U i →
        r z ∈ (LP.pull θ).U K → gw w r z i K = gw ψ (r ≫ θ) z i (K PUnit.unit) := by
  subst hG
  have hle : ∀ (J : PUnit → LL.ι) (K : PUnit → LP.ι),
      (LL.pull (θ ≫ φ)).U J ⊓ (LP.pull θ).U K ≤ θ ⁻¹ᵁ ((LL.pull φ).U J ⊓ LP.U (K PUnit.unit)) :=
    fun J K x hx => ⟨(mem_pull (F := φ)).2 ((mem_pull (F := θ ≫ φ)).1 hx.1), (mem_pull (F := θ)).1 hx.2⟩
  obtain ⟨w, hw⟩ : ∃ w : LB.Iso (LP.pull θ) (LL.pull (θ ≫ φ)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : LL.ι) (K : PUnit → LP.ι), (θ ≫ φ) (r z) ∈ LL.U i →
        r z ∈ (LP.pull θ).U K → gw w r z i K = gw ψ (r ≫ θ) z i (K PUnit.unit) :=
    ⟨⟨fun p => res (hle p.1 p.2) (pullU θ _ (ψ.s (p.1, p.2 PUnit.unit)))⟩, fun Z r z i K hi hK =>
      (gm_res r z (hle (fun _ => i) K) ⟨mem_pull.2 hi, hK⟩ _).trans
        (gm_pull r θ z _ (hle (fun _ => i) K ⟨mem_pull.2 hi, hK⟩) _)⟩
  refine ⟨w, fun Z r z j j' k k' hj hj' hk hk' => ?_, hw⟩
  rw [hw Z r z j k hj hk, hw Z r z j' k' hj' hk', gm_pull_g LP θ r z k k' hk hk',
    hψ Z (r ≫ θ) z j j' (k PUnit.unit) (k' PUnit.unit) hj hj' ((mem_pull (F := θ)).1 hk) ((mem_pull (F := θ)).1 hk'), Category.assoc]

theorem isoAsPullId {X : Scheme.{0}} {LL LM : LB X} (e : LB.Iso LM LL) (he : e.IsGen) :
    ∃ eP : LB.Iso LM (LL.pull (𝟙 X)), PGen eP ∧ ∀ (Y : Scheme.{0}) (f : Y ⟶ X) (y : Y) (i : LL.ι) (j : LM.ι),
      f y ∈ LL.U i → f y ∈ LM.U j → gw eP f y i j = gm f y (LL.U i ⊓ LM.U j) (e.s (i, j)) := by
  have hle : ∀ (J : PUnit → LL.ι) (j : LM.ι), (LL.pull (𝟙 X)).U J ⊓ LM.U j ≤ LL.U (J PUnit.unit) ⊓ LM.U j :=
    fun J j x hx => ⟨mem_pull.1 hx.1, hx.2⟩
  obtain ⟨eP, hP⟩ : ∃ eP : LB.Iso LM (LL.pull (𝟙 X)), ∀ (Y : Scheme.{0}) (f : Y ⟶ X) (y : Y) (i : LL.ι) (j : LM.ι),
      f y ∈ LL.U i → f y ∈ LM.U j → gw eP f y i j = gm f y (LL.U i ⊓ LM.U j) (e.s (i, j)) :=
    ⟨⟨fun p => res (hle p.1 p.2) (e.s (p.1 PUnit.unit, p.2))⟩, fun Y f y i j hi hj =>
      gm_res f y (hle (fun _ => i) j) ⟨mem_pull.2 hi, hj⟩ _⟩
  refine ⟨eP, fun Y f y j j' k k' hj hj' hk hk' => ?_, hP⟩
  have hm : f y ∈ LL.U j ⊓ LM.U k ⊓ (LL.U j' ⊓ LM.U k') := ⟨⟨hj, hk⟩, hj', hk'⟩
  have hm' : f y ∈ (LB.div LL LM).U (j, k) ⊓ (LB.div LL LM).U (j', k') := hm
  have h1 := congrArg (gm f y ((LB.div LL LM).U (j, k) ⊓ (LB.div LL LM).U (j', k'))) (he (j, k) (j', k'))
  have hd : gm f y ((LB.div LL LM).U (j, k) ⊓ (LB.div LL LM).U (j', k')) ((LB.div LL LM).g (j, k) (j', k')) =
      gm f y (LL.U j ⊓ LL.U j') (LL.g j j') * (gm f y (LM.U k ⊓ LM.U k') (LM.g k k'))⁻¹ :=
    (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res f y _ hm' _)
      ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res f y _ hm' _))))
  rw [hP Y f y j k hj hk, hP Y f y j' k' hj' hk', Category.comp_id]
  exact (gm_res f y inf_le_left hm' _).symm.trans (h1.trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) hd (gm_res f y inf_le_right hm' _))))

theorem isoCancelGerm : ∀ {Y XA XG : Scheme.{0}} (θ : Y ⟶ XA) (φ : XA ⟶ XG) (fst : Y ⟶ XG), θ ≫ φ = fst →
    ∀ (LP : LB XA) (LL LM : LB XG), LP.IsLB → LL.IsLB → LM.IsLB →
    ∀ (ψ : LB.Iso LP (LL.pull φ)) (e : LB.Iso LM LL), ψ.IsGen → e.IsGen →
    ∃ w₀ : LB.Iso (LP.pull θ) (LM.pull fst), w₀.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : LL.ι) (j : LM.ι) (k : LP.ι),
        fst (r z) ∈ LL.U i → fst (r z) ∈ LM.U j → θ (r z) ∈ LP.U k →
        gw w₀ r z j (fun _ => k) = (gm (r ≫ fst) z (LL.U i ⊓ LM.U j) (e.s (i, j)))⁻¹ * gw ψ (r ≫ θ) z i k := by
  intro Y XA XG θ φ fst hfst LP LL LM hP hL hM ψ e hψ he
  obtain ⟨w'', hw'', hv''⟩ := pullIsoAlong θ φ (fst ≫ 𝟙 XG) (by rw [Category.comp_id, hfst]) ψ
    ((isGen_iff ψ).1 hψ)
  obtain ⟨eP, heP, hvP⟩ := isoAsPullId e he
  obtain ⟨w₀, T⟩ := exists_cancel hL eP w'' heP hw'' hM (pull_isLB hP θ)
  refine ⟨w₀, (isGen_iff w₀).2 (T.pgen_cancel hL heP hw''), fun Z r z i j k hi hj hk => ?_⟩
  have t := T Z r z i j (fun _ => k) hi hj (mem_pull.2 hk)
  rw [hv'' Z r z i (fun _ => k) hi (mem_pull.2 hk), hvP Z (r ≫ fst) z i j hi hj] at t
  rw [t, inv_mul_cancel_left]

end GlobalTheory.IsoComp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoDualOfAffinePairing
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (resG_resG resG_self homOfLinear fun_ext_of_cover exists_fun_of_cover)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.VB

namespace GlobalTheory.AffinePairingGlue

variable {T : Scheme.{0}} {H : T.Modules}

theorem exists_affine_le {V : T.Opens} {x : T} (hx : x ∈ V) :
    ∃ W : T.Opens, IsAffineOpen W ∧ x ∈ W ∧ W ≤ V := by
  obtain ⟨W, hW, hxW, hWV⟩ := Opens.isBasis_iff_nbhd.1 T.isBasis_affineOpens hx
  exact ⟨W, hW, hxW, hWV⟩

theorem le_iSup_affine (V : T.Opens) :
    V ≤ ⨆ W : {W : T.Opens // IsAffineOpen W ∧ W ≤ V}, W.1 := fun x hx => by
  obtain ⟨W, hW, hxW, hWV⟩ := exists_affine_le hx
  exact Opens.mem_iSup.2 ⟨⟨W, hW, hWV⟩, hxW⟩

theorem fun_ext_affine {V : T.Opens} {a a' : Γ(T, V)}
    (e : ∀ (W : T.Opens) (_ : IsAffineOpen W) (h : W ≤ V), resG T h a = resG T h a') : a = a' :=
  fun_ext_of_cover (fun W : {W : T.Opens // IsAffineOpen W ∧ W ≤ V} => W.1) (fun W => W.2.2)
    (le_iSup_affine V) fun W => e W.1 W.2.1 W.2.2

variable (b : ∀ (V : T.Opens), IsAffineOpen V → (Γ(H, V) →ₗ[Γ(T, V)] Γ(H, V) →ₗ[Γ(T, V)] Γ(T, V)))
  (hb : ∀ (V V' : T.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (h : V' ≤ V)
    (s t : Γ(H, V)), b V' hV' (resM H h s) (resM H h t) = resG T h (b V hV s t))

include hb in

theorem exists_glued (V : T.Opens) (s t : Γ(H, V)) : ∃ a : Γ(T, V),
    ∀ (W : T.Opens) (hW : IsAffineOpen W) (h : W ≤ V),
      resG T h a = b W hW (resM H h s) (resM H h t) := by
  obtain ⟨a, ha⟩ := exists_fun_of_cover (fun W : {W : T.Opens // IsAffineOpen W ∧ W ≤ V} => W.1)
    (fun W => W.2.2) (le_iSup_affine V)
    (fun W => b W.1 W.2.1 (resM H W.2.2 s) (resM H W.2.2 t)) fun k l =>
      fun_ext_affine fun W hW h => by
        rw [resG_resG, resG_resG, ← hb _ _ k.2.1 hW, ← hb _ _ l.2.1 hW]
        simp only [resM_resM]
  exact ⟨a, fun W hW h => ha ⟨W, hW, h⟩⟩

def glued (V : T.Opens) (s t : Γ(H, V)) : Γ(T, V) := (exists_glued b hb V s t).choose

theorem resG_glued {V W : T.Opens} (hW : IsAffineOpen W) (h : W ≤ V) (s t : Γ(H, V)) :
    resG T h (glued b hb V s t) = b W hW (resM H h s) (resM H h t) :=
  (exists_glued b hb V s t).choose_spec W hW h

theorem glued_affine {V : T.Opens} (hV : IsAffineOpen V) (s t : Γ(H, V)) :
    glued b hb V s t = b V hV s t := by
  have := resG_glued b hb hV le_rfl s t
  rwa [resG_self, resM_self, resM_self] at this

theorem glued_res {V W : T.Opens} (h : W ≤ V) (s t : Γ(H, V)) :
    glued b hb W (resM H h s) (resM H h t) = resG T h (glued b hb V s t) :=
  fun_ext_affine fun U hU h' => by
    rw [resG_resG, resG_glued b hb hU, resG_glued b hb hU, resM_resM, resM_resM]

def gluedBilin (V : T.Opens) : Γ(H, V) →ₗ[Γ(T, V)] Γ(H, V) →ₗ[Γ(T, V)] Γ(T, V) :=
  LinearMap.mk₂ Γ(T, V) (glued b hb V)
    (fun s s' t => fun_ext_affine fun U hU h => by
      simp only [map_add, resG_glued b hb hU, LinearMap.add_apply])
    (fun a s t => fun_ext_affine fun U hU h => by
      simp only [smul_eq_mul, map_mul, resG_glued b hb hU, resM_smul, map_smul,
        LinearMap.smul_apply])
    (fun s t t' => fun_ext_affine fun U hU h => by
      simp only [map_add, resG_glued b hb hU])
    (fun a s t => fun_ext_affine fun U hU h => by
      simp only [smul_eq_mul, map_mul, resG_glued b hb hU, resM_smul, map_smul])

def toDual : H ⟶ dual H :=
  homOfLinear (fun V =>
    { toFun s := dualMk (fun W h => gluedBilin b hb W (resM H h s))
        fun W W' h h' t => by
          change glued b hb W' _ _ = resG T h' (glued b hb W _ _)
          rw [← glued_res, resM_resM]
      map_add' := fun s t => dual_ext fun W h u => by
        change gluedBilin b hb W (resM H h (s + t)) u = _
        rw [map_add, map_add]; rfl
      map_smul' := fun a s => dual_ext fun W h u => by
        change gluedBilin b hb W (resM H h (a • s)) u = _
        rw [resM_smul, map_smul]; rfl })
    fun h s => dual_ext fun W h' u =>
      congrArg (fun z => glued b hb W z u) (resM_resM h h' s)

theorem dualApp_toDual {V W : T.Opens} (h : W ≤ V) (s : Γ(H, V)) (t : Γ(H, W)) :
    dualApp ((toDual b hb).app V s) h t = glued b hb W (resM H h s) t := rfl

theorem dualApp_toDual_affine {V : T.Opens} (hV : IsAffineOpen V) (s t : Γ(H, V)) :
    dualApp ((toDual b hb).app V s) le_rfl t = b V hV s t := by
  rw [dualApp_toDual, resM_self, glued_affine]

theorem bijective_toDual_app {r : ℕ} {U V : T.Opens} {e : Fin r → Γ(H, U)} (he : IsFrame e)
    (h : V ≤ U) (hV : IsAffineOpen V) (hp : (b V hV).IsPerfPair) :
    Function.Bijective ((toDual b hb).app V) := by
  refine ⟨fun s s' hs => hp.bijective_left.1 (LinearMap.ext fun t => ?_), fun l => ?_⟩
  · rw [← dualApp_toDual_affine b hb hV, ← dualApp_toDual_affine b hb hV, hs]
  · obtain ⟨s, hs⟩ := hp.bijective_left.2 (dualApp l le_rfl)
    exact ⟨s, he.dual_ext h fun i => by rw [dualApp_toDual_affine b hb hV, hs]⟩

theorem isIso_toDual {r : ℕ} (hH : IsVB H r)
    (hp : ∀ (V : T.Opens) (hV : IsAffineOpen V), (b V hV).IsPerfPair) : IsIso (toDual b hb) := by
  have key (W : T.Opens) (x : T) (hx : x ∈ W) : ∃ V : T.Opens, x ∈ V ∧ V ≤ W ∧
      Function.Bijective ((toDual b hb).app V) := by
    obtain ⟨U, e, hxU, he⟩ := hH x
    obtain ⟨V, hV, hxV, hle⟩ := exists_affine_le (V := W ⊓ U) ⟨hx, hxU⟩
    exact ⟨V, hxV, hle.trans inf_le_left,
      bijective_toDual_app b hb he (hle.trans inf_le_right) hV (hp V hV)⟩
  have : Mono (toDual b hb) := QCoh.mono_of_locally_app_injective _ fun W x hx =>
    have ⟨V, h₁, h₂, h₃⟩ := key W x hx
    ⟨V, h₁, h₂, h₃.1⟩
  have : Epi (toDual b hb) := QCoh.epi_of_locally_app_surjective _ fun W x hx =>
    have ⟨V, h₁, h₂, h₃⟩ := key W x hx
    ⟨V, h₁, h₂, h₃.2⟩
  exact isIso_of_mono_of_epi _

theorem comp_toDual_comp_dualMap {F : T.Modules} (i : F ⟶ H)
    (hi : ∀ (V : T.Opens) (hV : IsAffineOpen V) (x y : Γ(F, V)),
      b V hV (i.app V x) (i.app V y) = 0) : i ≫ toDual b hb ≫ dualMap i = 0 := by
  ext V x : 3
  refine dual_ext fun W h y => fun_ext_affine fun U hU h' => ?_
  change resG T h' (glued b hb W (resM H h (i.app V x)) (i.app W y)) = resG T h' 0
  rw [resG_glued b hb hU, resM_resM, ← app_resM, ← app_resM, hi, map_zero]

theorem exists_iso_dual_of_affine_pairing :
    ∀ (T : Scheme.{0}) (H : T.Modules) (r : ℕ), GlobalTheory.VB.IsVB H r →
    ∀ (b : ∀ (V : T.Opens), IsAffineOpen V → (Γ(H, V) →ₗ[Γ(T, V)] Γ(H, V) →ₗ[Γ(T, V)] Γ(T, V))),
      (∀ (V V' : T.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (h : V' ≤ V) (s t : Γ(H, V)),
          b V' hV' (GlobalTheory.Twist.resM H h s) (GlobalTheory.Twist.resM H h t) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG T h (b V hV s t)) →
      (∀ (V : T.Opens) (hV : IsAffineOpen V), (b V hV).IsPerfPair) →
      ∀ (F : T.Modules) (i : F ⟶ H),
        (∀ (V : T.Opens) (hV : IsAffineOpen V) (x y : Γ(F, V)), b V hV (i.app V x) (i.app V y) = 0) →
        ∃ β : H ⟶ GlobalTheory.VB.dual H, IsIso β ∧ i ≫ β ≫ GlobalTheory.VB.dualMap i = 0 ∧
          ∀ (V : T.Opens) (hV : IsAffineOpen V) (s t : Γ(H, V)), GlobalTheory.VB.dualApp (β.app V s) le_rfl t = b V hV s t :=
  fun _ _ _ hH b hb hp _ i hi =>
    ⟨toDual b hb, isIso_toDual b hb hH hp, comp_toDual_comp_dualMap b hb i hi,
      fun _ hV s t => dualApp_toDual_affine b hb hV s t⟩

end GlobalTheory.AffinePairingGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLambdaPolarisationSiegelObjectCharZeroFiel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.SiegelSqrtField
open MonObj GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.AbLaw GlobalTheory.SiegelSqrt GlobalTheory.SiegelPullComp GlobalTheory.SiegelRingChange

theorem exists_sqOf_of_dim (hL : Out.Laws) (h k : ℕ) (o : Type) [CommRing o] (ζ : o) (R : Type) [CommRing R]
    [Algebra ℚ R] [IsNoetherianRing R] (β : o →+* R) (c₀ : SiegPre h k ζ (spMap β))
    (hd : SmoothOfRelativeDimension h c₀.A.hom) (hc₀ : c₀.Principal) :
    ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁) (P : Out.PolAV (Sp R₁)) (φ : P.A.left ⟶ c₀.A.left),
      (Module.Finite R R₁ ∧ Algebra.Etale R R₁ ∧ Module.FaithfullyFlat R R₁) ∧
        SqOf P c₀ (spMap (algebraMap R R₁)) φ := by
  have h2 : IsUnit ((2 : ℕ) : R) := by
    have := (IsUnit.mk0 ((2 : ℕ) : ℚ) (by norm_num)).map (algebraMap ℚ R)
    rwa [map_natCast] at this
  obtain ⟨R', _, _, ⟨f₁, e₁, l₁⟩, H₁⟩ := GlobalTheory.T.exists_finiteEtale_cover_constant_torsion R c₀.A h 2 c₀.ab hd h2
  obtain ⟨c', m', hc'⟩ := pull_sieg (spMap ((algebraMap R R').comp β)) (spMap (algebraMap R R'))
    (SiegelRingChange.spMap_comp' _ _).symm c₀ hc₀
  have m'' := m'
  obtain ⟨φ', -, g', -⟩ := m''
  obtain ⟨i₀, hi₀⟩ := H₁ c'.A φ' g'
  letI : Algebra ℚ R' := ((algebraMap R R').comp (algebraMap ℚ R)).toAlgebra
  haveI : IsNoetherianRing R' := Algebra.FiniteType.isNoetherianRing R R'
  obtain ⟨R₁, _, _, ⟨f₂, e₂, l₂⟩, H₂⟩ := GlobalTheory.T.exists_symmetric_linearisation_square_diagonalBundle hL h k o ζ R' _ c' h i₀ hc'
  obtain ⟨c₁, m₁, hc₁⟩ := pull_sieg (spMap ((algebraMap R' R₁).comp ((algebraMap R R').comp β)))
    (spMap (algebraMap R' R₁)) (SiegelRingChange.spMap_comp' _ _).symm c' hc'
  have m₁' := m₁
  obtain ⟨φ₁, φ₂, g₁, sq₁, w₁, -⟩ := m₁'
  obtain ⟨i, hi, li⟩ := exists_pull_labels g₁ 2 i₀ hi₀
  letI : Algebra ℚ R₁ := ((algebraMap R' R₁).comp (algebraMap ℚ R')).toAlgebra
  haveI : IsNoetherianRing R₁ := Algebra.FiniteType.isNoetherianRing R' R₁
  obtain ⟨u, j, huj⟩ := H₂ c₁.A φ₁ i _ g₁ hi rfl
  obtain ⟨p₁, p₂, p₃, p₄⟩ := GlobalTheory.abelianScheme_id_pow_finite_etale_surjective _ c₁.A 2 c₁.ab (isUnit_two_sections R₁)
  have hψ : ∀ {T : Over (Sp R₁)} (x : T ⟶ c₁.A), x ≫ ((𝟙 c₁.A) ^ 2 : c₁.A ⟶ c₁.A) = x ^ 2 := fun x => by
    rw [MonObj.comp_pow, Category.comp_id]
  have two : ∀ a : Multiplicative (Fin (2 * h) → ZMod 2), a ^ 2 = 1 := fun a => by
    apply Multiplicative.toAdd.injective
    funext x
    simp only [toAdd_pow, toAdd_one, Pi.smul_apply, Pi.zero_apply]
    generalize (Multiplicative.toAdd a x) = y
    revert y; decide
  have hD : (c'.diag.pull φ₁).IsLB := pull_isLB (diag_isLB c') _
  obtain ⟨M, hM, iM, sM⟩ := GlobalTheory.T.exists_descent_symmetric_linearised_bundle _ c₁.A c₁.A ((𝟙 c₁.A) ^ 2) _ i (lbPow (c'.diag.pull φ₁) 2)
    (GlobalTheory.isLB_lbPow hD 2) p₁ p₂ p₃ p₄ (fun a => by rw [hψ, ← map_pow, two, map_one])
    (fun K _ _ t => ⟨fun x => by rw [hψ]; exact (li K t).1 x, (li K t).2⟩) u j huj
  have iM' := (GlobalTheory.lbIso_lbPow (diag_iso sq₁ w₁) 2).trans (GlobalTheory.isLB_lbPow (diag_isLB c₁) 2) (GlobalTheory.isLB_lbPow hD 2)
    (pull_isLB hM _) iM
  have hd₁ : SmoothOfRelativeDimension h c₁.A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (g₁.comp g').1 hd
  obtain ⟨P, φ, hP⟩ := GlobalTheory.T.exists_principalPolarization_symmetric_squareRoot hL h k o ζ R₁ _ c₁ M hc₁ hd₁ hM
    (GlobalTheory.T.lam_iso_of_doubling_pullback_eq_diagonal_sq hL h k o ζ R₁ _ c₁ M hc₁ hM iM') sM
  obtain ⟨ψ, hψ'⟩ := sqOf_of_pb hP (pb_comp m' m₁)
  letI : Algebra R R₁ := ((algebraMap R' R₁).comp (algebraMap R R')).toAlgebra
  haveI : IsScalarTower R R' R₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine ⟨R₁, inferInstance, inferInstance, P, ψ,
    ⟨Module.Finite.trans R' R₁, Algebra.Etale.comp R R' R₁, Module.FaithfullyFlat.trans R R' R₁⟩, ?_⟩
  have e : spMap (algebraMap R R₁) = 𝟙 _ ≫ spMap (algebraMap R' R₁) ≫ spMap (algebraMap R R') := by
    rw [Category.id_comp, ← SiegelRingChange.spMap_comp']
  rw [e]; exact hψ'

end GlobalTheory.SiegelSqrtField
end

namespace GlobalTheory.SiegelSqrtField
open MonObj GlobalTheory.SiegelSqrt GlobalTheory.SiegelPullComp GlobalTheory.SiegelRingChange

theorem exists_sqrt_field : ∀ (h k : ℕ) (o : Type) [CommRing o] (ζ : o) (S : Scheme.{0}) (s : S ⟶ Sp o) (c : SiegPre h k ζ s), c.Principal →
    ∀ (K : Type) [Field K] [CharZero K] (f : Sp K ⟶ S), ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra K R₁),
      Module.Finite K R₁ ∧ Nontrivial R₁ ∧ ∃ (P : PolAV (Sp R₁)) (α : P.A.left ⟶ c.A.left) (α₂ : (G2 P.A).left ⟶ (G2 c.A).left),
        IsGrpPullback P.A c.A (spMap (algebraMap K R₁) ≫ f) α ∧ IsSquare α α₂ ∧ LBIso (abelian₂ P.A P.L) (c.P.pull α₂) := by
  intro h k o _ ζ S s c hc K _ _ f
  obtain ⟨β, hβ⟩ : ∃ β : o →+* K, f ≫ s = spMap β :=
    ⟨(Spec.preimage (f ≫ s)).hom, by simp [spMap]⟩
  obtain ⟨c₀, m₀, hc₀⟩ := pull_sieg (spMap β) f hβ c hc
  obtain ⟨g, hg⟩ := GlobalTheory.AbVarRelDim.exists_relDim K c₀.A c₀.ab
  let c₁ : SiegPre g 2 (0 : K) (spMap (RingHom.id K)) :=
    { A := c₀.A, ab := c₀.ab, P := c₀.P, isLB := c₀.isLB, rig₁ := c₀.rig₁, rig₂ := c₀.rig₂, symm := c₀.symm,
      lev := fun _ => 1, lev_add := fun _ _ => (mul_one 1).symm, lev_tors := fun _ => one_pow _,
      geom := fun k _ _ x β' z _ hz => absurd (hz.trans (map_zero β')) z.ne_zero }
  have hc₁ : c₁.Principal := hc₀
  obtain ⟨R₁, _, _, P, φ, ⟨hfin, -, hff⟩, hP⟩ :=
    exists_sqOf_of_dim GlobalTheory.allSixLaws.1 g 2 K 0 K (RingHom.id K) c₁ hg hc₁
  obtain ⟨χ, χ₂, hχ, hs, hw, -⟩ := m₀
  obtain ⟨hφ, -, φ₂, hs', hw'⟩ := hP
  have lam : (abelian₂ P.A P.L).IsLB := LB.isLB_linComb P.isLB _ _
  refine ⟨R₁, inferInstance, inferInstance, hfin, ?_, P, φ ≫ χ, φ₂ ≫ χ₂, hφ.comp hχ, ⟨?_, ?_⟩, ?_⟩
  · haveI := Module.FaithfullyFlat.lTensor_nontrivial K R₁ K
    exact (TensorProduct.lid K R₁).injective.nontrivial
  · rw [Category.assoc, hs.1, ← Category.assoc, hs'.1, Category.assoc]
  · rw [Category.assoc, hs.2, ← Category.assoc, hs'.2, Category.assoc]
  · exact (hw'.trans lam (pull_isLB c₀.isLB _) (pull_isLB (pull_isLB c.isLB _) _) (iso_pull φ₂ hw)).trans
      lam (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c.isLB _) (iso_pull_pull c.isLB χ₂ φ₂)

end GlobalTheory.SiegelSqrtField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftPointAffineHomSectionsRingHomStatement
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_point_affineHom_sections_ringHom : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsAffineHom π], ∀ (U : Z.affineOpens) (V V' : Type) [CommRing V]
    [IsLocalRing V] [CommRing V'] [IsLocalRing V'] (ξ : Sp V ⟶ Z) (hξ : ⊤ ≤ ξ ⁻¹ᵁ U.1) (f : V →+* V')
    (ρ : Γ(Y, π ⁻¹ᵁ U.1) →+* V'),
    ρ.comp (π.app U.1).hom = f.comp (ξ.appLE U.1 ⊤ hξ ≫ (Scheme.ΓSpecIso (.of V)).hom).hom →
    ∃ ψ : Sp V' ⟶ Y, ψ ≫ π = spMap f ≫ ξ ∧
      ∀ I : Y.IdealSheafData, idlAlong I ψ = (I.ideal ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩).map ρ := by
  first | exact @GlobalTheory.AffinePointLift.exists_lift | exact GlobalTheory.AffinePointLift.exists_lift | (intros; apply GlobalTheory.AffinePointLift.exists_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtensionOverNormalQuasiProjectiveBaseStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extension_over_normal_quasi_projective_base : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Y₀ Y X : Scheme.{0}) (i : Y₀ ⟶ Y) (σ : Y ⟶ Sp R) (τ : X ⟶ Sp R) (t₀ : Y₀ ⟶ X), IsOpenImmersion i → IsDominant i → IsLocallyNoetherian Y → IsReduced Y → (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) → IsQProjOver τ → i ≫ σ = t₀ ≫ τ → (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (y : Sp V ⟶ Y) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y = x ≫ i → ∃ z : Sp V ⟶ X, spMap (algebraMap V K) ≫ z = x ≫ t₀) → (∀ y : Y, {z : X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' : Sp V ⟶ Y) (z' : Sp V ⟶ X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ i ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = y ∧ z' (IsLocalRing.closedPoint V) = z}.Finite) → ∃ t : Y ⟶ X, i ≫ t = t₀ ∧ t ≫ τ = σ := by
  first | (exact @GlobalTheory.ExtendNormal.exists_extension) | (exact GlobalTheory.ExtendNormal.exists_extension) | (intros; apply GlobalTheory.ExtendNormal.exists_extension  <;> assumption)
end


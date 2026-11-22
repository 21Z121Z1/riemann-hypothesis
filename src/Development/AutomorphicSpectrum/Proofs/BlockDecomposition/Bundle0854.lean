import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0653
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.SchemeModels
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.LBSpreads
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
import Formalism.RealPlaceAnalysis.Bundle0004
import Formalism.PeriodIntegrals.Bundle0022
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0132
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0128
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0079

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinCohStOfCmpSt
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.Hodge

theorem finCohSt_of_cmpSt : CmpSt → FinCohSt := by
  intro h R _ _ X s _ P _ _ S
  letI := GlobalTheory.algebraΓOfHom s
  have hf : ∀ p, Module.Finite R (GlobalTheory.coh (GlobalTheory.structureModule X) p) := fun p ↦
    GlobalTheory.ProperFinite.finite_coh_of_isProper s (GlobalTheory.structureModule X) p
  obtain ⟨⟨e₀⟩, hn⟩ := h R X s inferInstance P S
  refine ⟨?_, fun n ↦ ?_⟩
  · have := hf 0
    exact Module.Finite.equiv e₀.symm
  · obtain ⟨e⟩ := hn n
    have := hf (n + 1)
    exact Module.Finite.equiv e.symm

end GlobalTheory.CompanionTheory.Hodge
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstHypercohomologyBaseChange
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.HodgeAssembly

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}

theorem clForm_injective (s : X ⟶ Sp R) (hS : Stein (OAff s)) : Function.Injective (clForm s) := by
  refine (injective_iff_map_eq_zero _).2 fun ω h ↦ ?_
  obtain ⟨g, hg, hD⟩ := ofForm_eq_zero.1 h
  have h0 : d0 (OAff s) g = 0 := by
    funext T T' φ
    exact sub_eq_zero.2 (hg φ)
  obtain ⟨r, rfl⟩ := (hS.1 g).1 h0
  refine Subtype.ext (Subtype.ext (funext fun T ↦ ?_))
  refine (hD T).symm.trans ?_
  exact Derivation.map_algebraMap _ r

theorem vb_middle {M N P : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup P]
    [Module R P] (i : M →ₗ[R] N) (q : N →ₗ[R] P) (hi : Function.Injective i) (hq : Function.Surjective q)
    (hex : Function.Exact i q) {a b : ℕ} (hM : VB R M a) (hP : VB R P b) : VB R N (a + b) := by
  obtain ⟨f1, f2, f3⟩ := hM
  obtain ⟨g1, g2, g3⟩ := hP
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property q LinearMap.id hq
  let e : N ≃ₗ[R] M × P := (hex.splitSurjectiveEquiv hi ⟨σ, hσ⟩).1
  refine ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm, fun p ↦ ?_⟩
  rw [Module.rankAtStalk_eq_of_equiv e, Module.rankAtStalk_prod, Pi.add_apply, f3, g3]

theorem exists_abelian {S S' : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) {s' : X' ⟶ S'}
    {φ : X' ⟶ A.left} {f : S' ⟶ S} (h : IsPullback φ s' A.hom f) :
    ∃ _ : GrpObj (Over.mk s'), IsAbelianScheme (Over.mk s') := by
  let e : Over.mk s' ≅ (Over.pullback f).obj A := Over.isoMk h.isoPullback h.isoPullback_hom_snd
  let I : GrpObj (Over.mk s') := GrpObj.ofIso e.symm
  have : IsMonHom e.symm.hom := CategoryTheory.isMonHom_ofIso e.symm
  have : IsMonHom e.hom := inferInstanceAs (IsMonHom e.symm.inv)
  exact ⟨I, GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA
    ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback A f))⟩

theorem bijective_middle {M N P M' N' P' : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']
    [AddCommGroup P'] [Module R P'] (i : M →ₗ[R] N) (q : N →ₗ[R] P) (i' : M' →ₗ[R] N') (q' : N' →ₗ[R] P')
    (L : N →ₗ[R] N') (eM : M ≃ₗ[R] M') (eP : P ≃ₗ[R] P') (hex : Function.Exact i q)
    (hq : Function.Surjective q) (hex' : Function.Exact i' q') (hi' : Function.Injective i')
    (s₁ : ∀ m, L (i m) = i' (eM m)) (s₂ : ∀ n, q' (L n) = eP (q n)) : Function.Bijective L := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun z hz ↦ ?_, fun x ↦ ?_⟩
  · have h1 : q z = 0 := by
      apply eP.injective
      rw [← s₂, hz, map_zero, map_zero]
    obtain ⟨m, rfl⟩ := (hex z).1 h1
    have h2 : eM m = 0 := hi' (by rw [← s₁, hz, map_zero])
    rw [(map_eq_zero_iff eM eM.injective).1 h2, map_zero]
  · obtain ⟨z, hz⟩ := hq (eP.symm (q' x))
    have h1 : q' (x - L z) = 0 := by
      rw [map_sub, s₂, hz, LinearEquiv.apply_symm_apply, sub_self]
    obtain ⟨m', hm'⟩ := (hex' _).1 h1
    refine ⟨z + i (eM.symm m'), ?_⟩
    rw [map_add, s₁, LinearEquiv.apply_symm_apply, hm']
    abel

section BaseChange

variable [Algebra R R'] {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X}

def clG (s : X ⟶ Sp R) (hcl : ClosedForm s = ⊤) : GlobForm s →ₗ[R] HH1 s :=
  clForm s ∘ₗ (LinearEquiv.ofTop _ hcl).symm.toLinearMap

theorem clG_apply (s : X ⟶ Sp R) (hcl : ClosedForm s = ⊤) (ω : GlobForm s) :
    clG s hcl ω = clForm s ⟨ω, hcl ▸ trivial⟩ := rfl

theorem clG_injective (s : X ⟶ Sp R) (hcl : ClosedForm s = ⊤) (hi : Function.Injective (clForm s)) :
    Function.Injective (clG s hcl) :=
  hi.comp (LinearEquiv.ofTop _ hcl).symm.injective

theorem exact_clG (s : X ⟶ Sp R) (hcl : ClosedForm s = ⊤) : Function.Exact (clG s hcl) (toHO1 s) := by
  intro c
  change c ∈ CechHodgeFiltration s ↔ _
  rw [cechHodgeFiltration_eq_range]
  constructor
  · rintro ⟨ω, rfl⟩
    exact ⟨ω.1, congrArg (clForm s) (Subtype.ext rfl)⟩
  · rintro ⟨ω, rfl⟩
    exact ⟨_, rfl⟩

theorem first_hypercohomology_base_change (w : φ ≫ s = s' ≫ spMap (algebraMap R R')) (hcl : ClosedForm s = ⊤)
    (hcl' : ClosedForm s' = ⊤) (hsurj : Function.Surjective (toHO1 s))
    (hinj' : Function.Injective (clForm s'))
    (eF : R' ⊗[R] GlobForm s ≃ₗ[R'] GlobForm s') (hF : ∀ c, IsPullForm w c (eF (1 ⊗ₜ c)))
    (eO : R' ⊗[R] HO1 s ≃ₗ[R'] HO1 s') (hO : ∀ c, IsPullO w c (eO (1 ⊗ₜ c))) :
    ∃ e : R' ⊗[R] HH1 s ≃ₗ[R'] HH1 s', ∀ c, IsPull1 w c (e (1 ⊗ₜ c)) := by
  let L : R' ⊗[R] HH1 s →ₗ[R'] HH1 s' := GlobalTheory.DeRham.liftSemi (pullHH1 w)
  have hL : ∀ c, L (1 ⊗ₜ c) = pullHH1 w c := fun c ↦ by
    rw [show L (1 ⊗ₜ c) = (1 : R') • pullHH1 w c from rfl, one_smul]
  have k₁ : ∀ ω, pullHH1 w (clG s hcl ω) = clG s' hcl' (eF (1 ⊗ₜ ω)) := fun ω ↦
    (IsPull1.eq_pullHH1 w (IsPullForm.cl (ω := ⟨ω, hcl ▸ trivial⟩)
      (ω' := ⟨eF (1 ⊗ₜ ω), hcl' ▸ trivial⟩) (hF ω))).symm
  have k₂ : ∀ c, toHO1 s' (pullHH1 w c) = eO (1 ⊗ₜ toHO1 s c) := fun c ↦
    (IsPullO.eq_pullHO1 w (IsPull1.toO (isPull1_pullHH1 w c))).trans
      (IsPullO.eq_pullHO1 w (hO (toHO1 s c))).symm
  have hex : Function.Exact ((clG s hcl).baseChange R') ((toHO1 s).baseChange R') := by
    have := lTensor_exact R' (exact_clG s hcl) hsurj
    simpa only [LinearMap.baseChange_eq_ltensor] using this
  have hq : Function.Surjective ((toHO1 s).baseChange R') := by
    have := LinearMap.lTensor_surjective R' hsurj
    simpa only [LinearMap.baseChange_eq_ltensor] using this
  have hb : Function.Bijective L := by
    refine bijective_middle ((clG s hcl).baseChange R') ((toHO1 s).baseChange R') (clG s' hcl') (toHO1 s') L eF eO
      hex hq (exact_clG s' hcl') (clG_injective s' hcl' hinj') (fun m ↦ ?_) fun n ↦ ?_
    · induction m using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul x ω =>
        have e : x ⊗ₜ[R] ω = x • ((1 : R') ⊗ₜ[R] ω) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
        rw [LinearMap.baseChange_tmul, e, map_smul, map_smul, ← k₁]
        rw [show L (x ⊗ₜ clG s hcl ω) = x • pullHH1 w (clG s hcl ω) from rfl]
    · induction n using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul x c =>
        have e : x ⊗ₜ[R] toHO1 s c = x • ((1 : R') ⊗ₜ[R] toHO1 s c) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
        rw [LinearMap.baseChange_tmul, e, map_smul, ← k₂]
        rw [show L (x ⊗ₜ c) = x • pullHH1 w c from rfl, map_smul]
  refine ⟨LinearEquiv.ofBijective L hb, fun c ↦ ?_⟩
  rw [LinearEquiv.ofBijective_apply, hL]
  exact isPull1_pullHH1 w c

end BaseChange

theorem abelianHodgeDeRham_of_statements : SteinSt → ParSt → H1StructureBundle → DegenSt → WedgeHypSt → OBCSt → FormBCSt →
    GlobalTheory.Published.AbelianHodgeDeRham := by
  intro hS hP hH hD hW hO hF R _ A _ g hA hg
  have s₀ : Stein (OAff A.hom) := hS R A g hA hg
  have p₀ : VB R (GlobForm A.hom) g := (hP R A g hA hg).2
  have h₀ : VB R (HO1 A.hom) g := hH R A g hA hg
  obtain ⟨hcl, hsurj⟩ : ClosedForm A.hom = ⊤ ∧ Function.Surjective (toHO1 A.hom) := hD R A g hA hg
  have hinj := clForm_injective A.hom s₀
  have v : VB R (HH1 A.hom) (g + g) := vb_middle (clG A.hom hcl) (toHO1 A.hom) (clG_injective A.hom hcl hinj) hsurj
    (exact_clG A.hom hcl) p₀ h₀
  refine ⟨⟨v.1, v.2.1, fun p ↦ by rw [two_mul]; exact v.2.2 p⟩, hW R A g hA hg, p₀, h₀, ⟨hcl, hinj, hsurj⟩,
    fun R' _ _ X' s' φ h ↦ ?_⟩
  obtain ⟨eO, heO⟩ := hO R A g hA hg R' X' s' φ h
  obtain ⟨eF, heF⟩ := hF R A g hA hg R' X' s' φ h
  obtain ⟨_, hA'⟩ := exists_abelian A hA h
  have hg' : SmoothOfRelativeDimension g (Over.mk s').hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := g)).of_isPullback h hg
  have s₁ : Stein (OAff s') := hS R' (Over.mk s') g hA' hg'
  have hcl' : ClosedForm s' = ⊤ := (hD R' (Over.mk s') g hA' hg').1
  exact ⟨first_hypercohomology_base_change h.w hcl hcl' hsurj (clForm_injective s' s₁) eF heF eO heO, ⟨eF, heF⟩, ⟨eO, heO⟩⟩

end GlobalTheory.CompanionTheory.HodgeAssembly
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasModelOfSpreading
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.SpreadingModels

namespace GlobalTheory.CompanionTheory.CubeModels

theorem model_refine {R R₀ R₁ : Type} [CommRing R] [CommRing R₀] [CommRing R₁] {φ : R₀ →+* R}
    {ψ : R₀ →+* R₁} {φ₁ : R₁ →+* R} (e : φ₁.comp ψ = φ) (ft : Algebra.FiniteType ℤ R₁)
    {Y Y₀ : Scheme.{0}} {f : Y ⟶ Spec (CommRingCat.of R)} {f₀ : Y₀ ⟶ Spec (CommRingCat.of R₀)}
    {π : Y ⟶ Y₀} (hm : IsModel φ f f₀ π)
    (ρ : Y ⟶ pullback f₀ (Spec.map (CommRingCat.ofHom ψ)))
    (h₁ : ρ ≫ pullback.fst _ _ = π)
    (h₂ : ρ ≫ pullback.snd _ _ = f ≫ Spec.map (CommRingCat.ofHom φ₁)) :
    IsModel φ₁ f (pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ))) ρ := by
  obtain ⟨-, l, q, s, sq⟩ := hm
  have hc : Spec.map (CommRingCat.ofHom φ) =
      Spec.map (CommRingCat.ofHom φ₁) ≫ Spec.map (CommRingCat.ofHom ψ) := by
    subst e
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  refine ⟨ft, inferInstance, inferInstance, inferInstance, ?_⟩
  refine IsPullback.of_right (h₁₂ := pullback.fst f₀ (Spec.map (CommRingCat.ofHom ψ)))
    (v₁₃ := f₀) (h₂₂ := Spec.map (CommRingCat.ofHom ψ)) ?_ h₂ (IsPullback.of_hasPullback _ _)
  rw [h₁, ← hc]
  exact sq

def refineMap {R R₀ R₁ : Type} [CommRing R] [CommRing R₀] [CommRing R₁] {φ : R₀ →+* R}
    {ψ : R₀ →+* R₁} {φ₁ : R₁ →+* R} (e : φ₁.comp ψ = φ)
    {Y Y₀ : Scheme.{0}} {f : Y ⟶ Spec (CommRingCat.of R)} {f₀ : Y₀ ⟶ Spec (CommRingCat.of R₀)}
    {π : Y ⟶ Y₀} (hm : IsModel φ f f₀ π) :
    Y ⟶ pullback f₀ (Spec.map (CommRingCat.ofHom ψ)) :=
  pullback.lift π (f ≫ Spec.map (CommRingCat.ofHom φ₁)) (by
    have hc : Spec.map (CommRingCat.ofHom φ) =
        Spec.map (CommRingCat.ofHom φ₁) ≫ Spec.map (CommRingCat.ofHom ψ) := by
      subst e
      rw [CommRingCat.ofHom_comp, Spec.map_comp]
    rw [Category.assoc, ← hc]
    exact hm.2.2.2.2.w)

theorem model_refine' {R R₀ R₁ : Type} [CommRing R] [CommRing R₀] [CommRing R₁] {φ : R₀ →+* R}
    {ψ : R₀ →+* R₁} {φ₁ : R₁ →+* R} (e : φ₁.comp ψ = φ) (ft : Algebra.FiniteType ℤ R₁)
    {Y Y₀ : Scheme.{0}} {f : Y ⟶ Spec (CommRingCat.of R)} {f₀ : Y₀ ⟶ Spec (CommRingCat.of R₀)}
    {π : Y ⟶ Y₀} (hm : IsModel φ f f₀ π) :
    IsModel φ₁ f (pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ))) (refineMap e hm) :=
  model_refine e ft hm _ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

theorem hasModel_of_spreads : GlobalTheory.SpreadingModels.SchemeModels → GlobalTheory.SpreadingModels.Spreads (fun _ _ f => Smooth f) →
    GlobalTheory.SpreadingModels.Spreads (fun _ _ f => IsProper f) → GlobalTheory.SpreadingModels.LBSpreads →
    ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)), Smooth f → IsProper f →
      ∀ M : LB Y, M.IsLB → GlobalTheory.SpreadingModels.HasModel f M := by
  intro hS hSm hPr hLB R _ Y f hsm hpr M hM
  obtain ⟨R₀, _, φ, Y₀, f₀, π, hm⟩ := hS R Y f inferInstance inferInstance inferInstance
  obtain ⟨R₁, _, ψ₁, φ₁, e₁, ft₁, sm₁⟩ := hSm R R₀ φ Y Y₀ f f₀ π hm hsm
  have m₁ := model_refine' e₁ ft₁ hm
  obtain ⟨R₂, _, ψ₂, φ₂, e₂, ft₂, pr₂⟩ := hPr R R₁ φ₁ Y _ f _ _ m₁ hpr
  have m₂ := model_refine' e₂ ft₂ m₁
  obtain ⟨R₃, _, ψ₃, φ₃, ρ, e₃, ft₃, r₁, r₂, M₃, hM₃, w, hw⟩ := hLB R R₂ φ₂ Y _ f _ _ m₂ M hM
  have m₃ := model_refine e₃ ft₃ m₂ ρ r₁ r₂
  have sm₁' : Smooth (pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ₁))) := sm₁
  have pr₂' : IsProper (pullback.snd (pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ₁)))
      (Spec.map (CommRingCat.ofHom ψ₂))) := pr₂
  refine ⟨R₃, inferInstance, Algebra.FiniteType.isNoetherianRing ℤ R₃, φ₃, _,
    pullback.snd (pullback.snd (pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ₁)))
      (Spec.map (CommRingCat.ofHom ψ₂))) (Spec.map (CommRingCat.ofHom ψ₃)), ρ,
    inferInstance, inferInstance, m₃.2.2.2.2, M₃, hM₃, w, hw⟩

end GlobalTheory.CompanionTheory.CubeModels
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KFinSmoothBoth
section
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.KFinSmoothBoth

theorem kFin_smooth_both : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsHCParam lam →
    Formalism.MainNotions.S.IsDS ε lam σ → ∀ v : H, Formalism.MainNotions.S.IsKFin ε σ v →
    v ∈ GlobalTheory.SmoothVecMod.smoothVec ε σ ∧ v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) σ := by
  intro n ε lam H _ _ σ _ hσ v hv
  have := hσ.1
  have h : Formalism.QuantumDeterminants.SmoothOnH (Formalism.REAL.Jm ε) fun g => σ g v :=
    GlobalTheory.Published.KFiniteVectorsUnitary.smoothOnH GlobalTheory.CompanionTheory.Published.kFiniteVectors_irreducibleUnitary_unitaryGroupPQ
      hσ.2.2.1 hσ.2.2.2.1 hv
  exact ⟨h, h⟩

end GlobalTheory.CompanionTheory.KFinSmoothBoth
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfAllOfModels
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.SpreadingModels

namespace GlobalTheory.CompanionTheory.SpreadingModels

theorem perfAll_of_models
    (hBase : ∀ {R₀ R : Type} [CommRing R₀] [CommRing R] (φ : R₀ →+* R) {Y₀ Y : Scheme.{0}}
      (f₀ : Y₀ ⟶ Spec (CommRingCat.of R₀)) (f : Y ⟶ Spec (CommRingCat.of R)) (π : Y ⟶ Y₀),
      IsPullback π f f₀ (Spec.map (CommRingCat.ofHom φ)) → ∀ (M₀ : LB Y₀), M₀.IsLB → Perf f₀ M₀ →
        Nonempty (Perf f (M₀.pull π)))
    (hIso : ∀ {R : Type} [CommRing R] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of R)) {M M' : LB Y},
      M.IsLB → M'.IsLB → ∀ (w : LB.Iso M M'), w.IsGen → Perf f M' → Nonempty (Perf f M))
    (hModel : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)), Smooth f → IsProper f →
      ∀ M : LB Y, M.IsLB → HasModel f M) : PerfAll := by
  intro R _ Y f hs hp M hM
  obtain ⟨R₀, _, _, φ, Y₀, f₀, π, hp₀, hf₀, hsq, M₀, hM₀, w, hw⟩ := hModel R Y f hs hp M hM
  haveI := hp₀
  haveI := hf₀
  obtain ⟨P₀⟩ := GlobalTheory.ProperFinite.nonempty_perf_of_isProper f₀ hM₀
  obtain ⟨P⟩ := hBase φ f₀ f π hsq M₀ hM₀ P₀
  exact hIso f hM (Geo.Tor.pull_isLB hM₀ π) w hw P

end GlobalTheory.CompanionTheory.SpreadingModels
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectBaseChange
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.SpreadingModels

namespace GlobalTheory.CompanionTheory.PerfBase

section Transfer

variable {X : Scheme.{0}}

theorem res_val {U V : X.Opens} (h : V ≤ U) (x : Γ(X, U)ˣ) : (res h x).val = rs X h x.val := rfl

def secMap {A B : LB X} (q : B.ι → A.ι) (hq : ∀ b, B.U b ≤ A.U (q b))
    (hg : ∀ b b', res (inf_le_inf (hq b) (hq b')) (A.g (q b) (q b')) = B.g b b') (s : LB.Sec A) : LB.Sec B where
  f := fun b => rs X (hq b) (s.f (q b))
  compat := fun b b' => by
    have h := congrArg (rs X (inf_le_inf (hq b) (hq b') : B.U b ⊓ B.U b' ≤ A.U (q b) ⊓ A.U (q b')))
      (s.compat (q b) (q b'))
    change rs X _ (rs X inf_le_left (s.f (q b))) =
      rs X _ ((A.g (q b) (q b')).val * rs X inf_le_right (s.f (q b'))) at h
    change rs X inf_le_left (rs X (hq b) (s.f (q b))) =
      (B.g b b').val * rs X inf_le_right (rs X (hq b') (s.f (q b')))
    rw [← hg, res_val]
    simp only [rs_rs, map_mul] at h ⊢
    exact h

theorem h1_vanishing_of_refinement {A B : LB X} (q : B.ι → A.ι) (hq : ∀ b, B.U b ≤ A.U (q b))
    (hg : ∀ b b', res (inf_le_inf (hq b) (hq b')) (A.g (q b) (q b')) = B.g b b') (hA : FirstCohomologyVanishes A) : FirstCohomologyVanishes B := by
  intro I V c hV hc φ hφ
  obtain ⟨ψ, hψ⟩ := hA I V (fun a => q (c a)) (fun a => (hV a).trans (hq _)) hc φ (by
    intro a b d
    have h := hφ a b d
    rw [← hg, res_val, rs_rs] at h
    exact h)
  refine ⟨ψ, fun a b => ?_⟩
  rw [hψ a b, ← hg (c a) (c b), res_val, rs_rs]

end Transfer

section PullPull

variable {X' Y Y₀ : Scheme.{0}} (M : LB Y₀) (π : Y ⟶ Y₀) (π' : X' ⟶ Y)

theorem le_unfold (j : (M.pull (π' ≫ π)).ι) :
    (M.pull (π' ≫ π)).U j ≤ ((M.pull π).pull π').U (fun _ => j) :=
  fun _ hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k

theorem le_fold (j : ((M.pull π).pull π').ι) :
    ((M.pull π).pull π').U j ≤ (M.pull (π' ≫ π)).U (fun u => j u u) :=
  fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (Set.mem_iInter.1 hy k) k

theorem g_pull_pull (j j' : ((M.pull π).pull π').ι)
    (h : ((M.pull π).pull π').U j ⊓ ((M.pull π).pull π').U j' ≤
      (π' ≫ π) ⁻¹ᵁ (M.U (j PUnit.unit PUnit.unit) ⊓ M.U (j' PUnit.unit PUnit.unit))) :
    ((M.pull π).pull π').g j j' = res h (pullU (π' ≫ π) _ (M.g (j PUnit.unit PUnit.unit) (j' PUnit.unit PUnit.unit))) := by
  refine (LB.lcg_pull (M.pull π) π' j j').trans ?_
  refine (congrArg (fun x => res (LB.wchart_pu_le (M.pull π) π' j j') (pullU π' _ x))
    (LB.lcg_pull M π (j PUnit.unit) (j' PUnit.unit))).trans ?_
  exact LB.pull_res_comp π' π _ _ _ _ _

theorem g_pull_comp (j j' : (M.pull (π' ≫ π)).ι)
    (h : (M.pull (π' ≫ π)).U j ⊓ (M.pull (π' ≫ π)).U j' ≤
      (π' ≫ π) ⁻¹ᵁ (M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit))) :
    (M.pull (π' ≫ π)).g j j' = res h (pullU (π' ≫ π) _ (M.g (j PUnit.unit) (j' PUnit.unit))) :=
  LB.lcg_pull M (π' ≫ π) j j'

theorem hg_unfold (j j' : (M.pull (π' ≫ π)).ι) :
    res (inf_le_inf (le_unfold M π π' j) (le_unfold M π π' j'))
      (((M.pull π).pull π').g (fun _ => j) (fun _ => j')) = (M.pull (π' ≫ π)).g j j' := by
  refine (congrArg (res _) (g_pull_pull M π π' (fun _ => j) (fun _ => j')
    (fun y hy => ⟨Set.mem_iInter.1 (Set.mem_iInter.1 hy.1 PUnit.unit) PUnit.unit,
      Set.mem_iInter.1 (Set.mem_iInter.1 hy.2 PUnit.unit) PUnit.unit⟩))).trans ?_
  exact (LB.res_res _ _ _).trans (g_pull_comp M π π' j j'
    (fun y hy => ⟨Set.mem_iInter.1 hy.1 PUnit.unit, Set.mem_iInter.1 hy.2 PUnit.unit⟩)).symm

theorem hg_fold (j j' : ((M.pull π).pull π').ι) :
    res (inf_le_inf (le_fold M π π' j) (le_fold M π π' j'))
      ((M.pull (π' ≫ π)).g (fun u => j u u) (fun u => j' u u)) = ((M.pull π).pull π').g j j' := by
  refine (congrArg (res _) (g_pull_comp M π π' (fun u => j u u) (fun u => j' u u)
    (fun y hy => ⟨Set.mem_iInter.1 hy.1 PUnit.unit, Set.mem_iInter.1 hy.2 PUnit.unit⟩))).trans ?_
  exact (LB.res_res _ _ _).trans (g_pull_pull M π π' j j'
    (fun y hy => ⟨Set.mem_iInter.1 (Set.mem_iInter.1 hy.1 PUnit.unit) PUnit.unit,
      Set.mem_iInter.1 (Set.mem_iInter.1 hy.2 PUnit.unit) PUnit.unit⟩)).symm

theorem h1_vanishing_pull_comp (hH : FirstCohomologyVanishes ((M.pull π).pull π')) : FirstCohomologyVanishes (M.pull (π' ≫ π)) :=
  h1_vanishing_of_refinement (A := (M.pull π).pull π') (B := M.pull (π' ≫ π)) (fun j _ => j) (le_unfold M π π') (hg_unfold M π π') hH

def secPullPull : LB.Sec (M.pull (π' ≫ π)) ≃ LB.Sec ((M.pull π).pull π') where
  toFun := secMap (fun j u => j u u) (le_fold M π π') (hg_fold M π π')
  invFun := secMap (fun j _ => j) (le_unfold M π π') (hg_unfold M π π')
  left_inv := fun s => by
    obtain ⟨sf, hs⟩ := s
    simp only [secMap, LB.Sec.mk.injEq]
    funext j
    rw [rs_rs, rs_self]
  right_inv := fun s => by
    obtain ⟨sf, hs⟩ := s
    simp only [secMap, LB.Sec.mk.injEq]
    funext j
    rw [rs_rs, rs_self]

end PullPull

theorem perf_pull {R₀ R : Type} [CommRing R₀] [CommRing R] (φ : R₀ →+* R) {Y₀ Y : Scheme.{0}}
    (f₀ : Y₀ ⟶ Spec (CommRingCat.of R₀)) (f : Y ⟶ Spec (CommRingCat.of R)) (π : Y ⟶ Y₀)
    (hπ : IsPullback π f f₀ (Spec.map (CommRingCat.ofHom φ))) (M₀ : LB Y₀) (_hM : M₀.IsLB) (P : Perf f₀ M₀) :
    Nonempty (Perf f (M₀.pull π)) := by
  have paste : ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π' : X' ⟶ Y)
      (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π' f' f (Spec.map (CommRingCat.ofHom g)) →
      IsPullback (π' ≫ π) f' f₀ (Spec.map (CommRingCat.ofHom (g.comp φ))) := by
    intro R' _ g X' π' f' h
    have h' := h.paste_horiz hπ
    rwa [← Spec.map_comp, ← CommRingCat.ofHom_comp] at h'
  have hD₀ : ∀ (R' : Type) [CommRing R'] (g : R →+* R'), (P.D₀.map φ).map g = P.D₀.map (g.comp φ) :=
    fun _ _ _ => by ext; rfl
  have hD₁ : ∀ (R' : Type) [CommRing R'] (g : R →+* R'), (P.D₁.map φ).map g = P.D₁.map (g.comp φ) :=
    fun _ _ _ => by ext; rfl
  exact ⟨{
    a := P.a
    b := P.b
    c := P.c
    D₀ := P.D₀.map φ
    D₁ := P.D₁.map φ
    comp := by rw [← Matrix.map_mul, P.comp, Matrix.map_zero _ (map_zero φ)]
    I := P.I
    W := fun i => π ⁻¹ᵁ P.W i
    ch := fun i _ => P.ch i
    le := fun i => le_pull M₀ π (P.le i)
    cover := by
      refine top_unique fun y _ => ?_
      have hy : π y ∈ ⨆ i, P.W i := by rw [P.cover]; trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
    u := fun k i => (π.app (P.W i)).hom (P.u k i)
    sec := fun R' _ g X' π' f' h => by
      obtain ⟨E₀, hE⟩ := P.sec R' (g.comp φ) X' (π' ≫ π) f' (paste R' g X' π' f' h)
      refine ⟨(Equiv.subtypeEquivRight (fun v => by rw [hD₀])).trans (E₀.trans (secPullPull M₀ π π')),
        fun v i => ?_⟩
      refine Eq.trans ?_ (hE ⟨v.1, by rw [← hD₀]; exact v.2⟩ i)
      change rs X' _ (rs X' _ _) = _
      rw [rs_rs]
      rfl
    exact := fun R' _ g X' π' f' h hH w hw => by
      rw [hD₁] at hw
      obtain ⟨v, hv⟩ := P.exact R' (g.comp φ) X' (π' ≫ π) f' (paste R' g X' π' f' h)
        (h1_vanishing_pull_comp M₀ π π' hH) w hw
      exact ⟨v, by rw [hD₀]; exact hv⟩ }⟩

end GlobalTheory.CompanionTheory.PerfBase
end
end


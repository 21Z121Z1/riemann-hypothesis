import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2605
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2604
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2188
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2657
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2554
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PotentiallyKnownOfSameLambdaBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2485
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0102
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2599
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2587
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2610
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2597
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1183
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1205
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2409
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2606
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2252
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2228
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2621
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2676
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0175

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointwiseGeneratorOfDualNumberLineBundleGeStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pointwiseGenerator_of_dualNumberLineBundleGenerator : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left), P.IsLB → ∀ v : epsR R ⟶ B, IsTangent v → ∀ T, IsEpsGen P v T → ∃ t, IsPtGen P (lift (fst A (epsR R)) (snd A (epsR R) ≫ v)) t := by
  first | exact @GlobalTheory.PtExt.exists_isPtGen_of_isEpsGen | exact GlobalTheory.PtExt.exists_isPtGen_of_isEpsGen | (intros; apply GlobalTheory.PtExt.exists_isPtGen_of_isEpsGen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointwiseLineBundleGeneratorOfTrivialPullbStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pointwiseLineBundleGenerator_of_trivial_pullback : ∀ (R : Type) [CommRing R] (X Y : Over (Sp R)) (L : LB X.left), L.IsLB → ∀ q : Y ⟶ X, GlobalTheory.AbLaw.Triv (L.pull q.left) → ∃ t, IsPtGen L q t := by
  first | exact @GlobalTheory.PtExt.exists_isPtGen | exact GlobalTheory.PtExt.exists_isPtGen | (intros; apply GlobalTheory.PtExt.exists_isPtGen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolFormBaseChange
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatModel.HalfLower

section Lin

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {O : Type} [CommRing O] [IsDomain O] {K : Type} [Field K] [Algebra O K] [IsFractionRing O K]
variable {H : Type} [AddCommGroup H] [Module O H] {c : Ideal (OF E)}

omit [NumberField E] [IsCMField E] in

theorem inK_injective [Module.Free O H] : Function.Injective (inK (O := O) K H) := by
  have h := (Module.Flat.rTensor_preserves_injective_linearMap (M := H) (Algebra.linearMap O K)
    (IsFractionRing.injective O K)).comp (TensorProduct.lid O H).symm.injective
  intro x y hxy
  apply h
  simpa [inK] using hxy

theorem bar_bar (σ : E →+* K) : bar (bar σ) = σ := by
  ext x; simp [bar]

omit [IsDomain O] [IsFractionRing O K] in

theorem baseChange_inK (B : LinearMap.BilinForm O H) (x y : H) :
    B.baseChange K (inK K H x) (inK K H y) = algebraMap O K (B x y) := by
  simp [inK, Algebra.smul_def]

omit [IsCMField E] [IsDomain O] [IsFractionRing O K] in

theorem form_act (ρ : orderC c →+* Module.End O H) (B : LinearMap.BilinForm O H) {σ : E →+* K} {f : H}
    (hf : f ∈ eigLat ρ σ) (a : orderC c) (x : H) : algebraMap O K (B x (ρ a f)) = σ a * algebraMap O K (B x f) := by
  have h : inK K H f ∈ eigK ρ σ := hf
  have h1 := Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 h a)
  have h2 : (ρ a).baseChange K (inK K H f) = inK K H (ρ a f) := by simp [inK]
  rw [← baseChange_inK, ← baseChange_inK, ← h2, h1, map_smul, smul_eq_mul]

theorem lower_eq [Module.Free O H] (ρ : orderC c →+* Module.End O H) (B : LinearMap.BilinForm O H) {D : O} (hD : D ≠ 0)
    {τ : E →+* K} {e f : H} (he : eigLat ρ τ = O ∙ e) (hf : f ∈ eigLat ρ (bar τ))
    (hsup : ∀ h : H, D • h ∈ ⨆ σ : E →+* K, eigLat ρ σ)
    (horth : ∀ σ σ' : E →+* K, σ' ≠ bar σ → ∀ x ∈ eigK ρ σ, ∀ y ∈ eigK ρ σ', B.baseChange K x y = 0)
    {N : Module.End K (K ⊗[O] H)} {M : Module.End O H} (hN : IsLower ρ τ e f N) (hM : IsScaledRestr D N M) (x : H) :
    B e f • M x = (D * B x f) • f := by
  have key : ∀ h ∈ ⨆ σ : E →+* K, eigLat ρ σ, B e f • M h = (D * B h f) • f := by
    intro h hh
    induction hh using Submodule.iSup_induction' with
    | mem σ h hh =>
      by_cases hσ : σ = τ
      · subst hσ
        rw [he] at hh
        obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.1 hh
        have hMe : M e = D • f := inK_injective (K := K) (by rw [hM, hN.1, map_smul, algebraMap_smul])
        simp only [map_smul, hMe, LinearMap.smul_apply, smul_eq_mul, smul_smul]
        congr 1; ring
      · have h1 : M h = 0 := inK_injective (K := K) (by rw [hM, hN.2 σ hσ _ hh, smul_zero, map_zero])
        have h2 : B h f = 0 := IsFractionRing.injective O K (by
          rw [← baseChange_inK, map_zero]
          exact horth σ (bar τ) (fun h' ↦ hσ (by rw [← bar_bar σ, ← h', bar_bar])) _ hh _ hf)
        simp [h1, h2]
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add, LinearMap.add_apply, smul_add, mul_add, add_smul, hx, hy]
  have h := key _ (hsup x)
  apply smul_right_injective H hD
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h ⊢
  rw [smul_comm D, h, smul_smul]

theorem lower_eq_of_scale [CharZero O] [Module.Free O H] (ρ : orderC c →+* Module.End O H) (B B' : LinearMap.BilinForm O H)
    {D : O} (hD : D ≠ 0)
    {τ : E →+* K} {e f : H} (he : eigLat ρ τ = O ∙ e) (hf : f ∈ eigLat ρ (bar τ))
    (hsup : ∀ h : H, D • h ∈ ⨆ σ : E →+* K, eigLat ρ σ)
    (horth : ∀ σ σ' : E →+* K, σ' ≠ bar σ → ∀ x ∈ eigK ρ σ, ∀ y ∈ eigK ρ σ', B.baseChange K x y = 0)
    {N : Module.End K (K ⊗[O] H)} {M : Module.End O H} (hN : IsLower ρ τ e f N) (hM : IsScaledRestr D N M)
    {n : ℕ} (hn : n ≠ 0) (a : orderC c) (hB : ∀ x y, (n : O) * B' x y = 2 * B x (ρ a y)) (h0 : B' e f ≠ 0) (x : H) :
    B' e f • M x = (D * B' x f) • f := by
  have hn' : (n : O) ≠ 0 := Nat.cast_ne_zero.2 hn
  have h1 : B e (ρ a f) * B x f = B x (ρ a f) * B e f := IsFractionRing.injective O K (by
    rw [map_mul, map_mul, form_act ρ B hf, form_act ρ B hf]; ring)
  have h2 : B' e f * B x f = B' x f * B e f :=
    mul_left_cancel₀ hn' (by linear_combination B x f * hB e f - B e f * hB x f + 2 * h1)
  have hβ : B e f ≠ 0 := fun hβ ↦ h0 (mul_left_cancel₀ hn' (by
    have : B e (ρ a f) = 0 := IsFractionRing.injective O K (by rw [form_act ρ B hf, hβ]; simp)
    rw [hB, this]; simp))
  apply smul_right_injective H hβ
  simp only
  rw [smul_comm, lower_eq ρ B hD he hf hsup horth hN hM, smul_smul, smul_smul]
  congr 1
  linear_combination D * h2

end Lin

theorem exists_polForm_baseChange {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R R' : Type} [CommRing R] [CommRing R']
    (σ : R →+* R') {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')} {p : X'.A.left ⟶ X.A.left}
    (hX : X'.IsPullBy X (spMap σ) p) (m : GrpMor (dp0 R) (𝟙 _) X.A (dp0 R') (𝟙 _) X'.A σ (spMap σ) p) (c : 𝔠.elt)
    {ψ : LinearMap.BilinForm R (HdR X.A)} (hψ : IsPolForm (dp0 R) (𝟙 _) X.A (X.diag c) ψ) :
    ∃ ψ' : LinearMap.BilinForm R' (HdR X'.A), IsPolForm (dp0 R') (𝟙 _) X'.A (X'.diag c) ψ' ∧
      ∀ x x' y y', m.Corr x x' → m.Corr y y' → ψ' x' y' = σ (ψ x y) := by
  obtain ⟨ψ', ⟨n, a, b, hch, he⟩, h'⟩ :=
    IsPolForm.pull_comp m (X.isLB c) (π := (lift (𝟙 X.A) (𝟙 X.A)).left) (L := X.P c) hψ
  obtain ⟨φ₂, hsq, hiso⟩ := hX.pol
  have e : (lift (𝟙 X'.A) (𝟙 X'.A)).left ≫ φ₂ = p ≫ (lift (𝟙 X.A) (𝟙 X.A)).left := by
    apply pullback.hom_ext
    · change _ ≫ (fst X.A X.A).left = _ ≫ (fst X.A X.A).left
      rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Over.comp_left,
        lift_fst]
      simp
    · change _ ≫ (snd X.A X.A).left = _ ≫ (snd X.A X.A).left
      rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc, ← Over.comp_left,
        lift_snd]
      simp
  have hI : LBIso (X'.diag c) ((X.P c).pull (p ≫ (lift (𝟙 X.A) (𝟙 X.A)).left)) :=
    GlobalTheory.GenSpread.lbIso_pull_of_lbIso (hiso c) _ e.symm
  exact ⟨ψ', ⟨n, a, b, (isChern_existsUnique_and_iso _ _ _ _ _).2 _ _ (pull_isLB (X.isLB c) _)
    (pull_isLB (X'.isLB c) _) hI.symm _ hch, he⟩, h'⟩

theorem corr_lower (hDR : GlobalTheory.Published.AbelianDeRham) {E : Type} [Field E] [NumberField E] [IsCMField E] {c : Ideal (OF E)}
    {𝔠 : FracId (FR E)} {R : Subring ℂ} {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
    {X₀ : Obj (FR E) 𝔠 (Sp R)} {X : Obj (FR E) 𝔠 (Sp ℂ)} {p : X.A.left ⟶ X₀.A.left} (cm : OAct (orderC c) X₀.A)
    (hrm : ∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF c a) = X₀.rm.act a)
    {n : ℕ} (eH : HdR X₀.A ≃ₗ[R] (Fin n → R)) {c₀ c₁ : 𝔠.elt} {ψ₀ ψR : LinearMap.BilinForm R (HdR X₀.A)} (hc₀ : (c₀ : FR E) ≠ 0)
    (hψ₀ : IsPolForm (dp0 R) (𝟙 _) X₀.A (X₀.diag c₀) ((2 : R) • ψ₀)) (hψR : IsPolForm (dp0 R) (𝟙 _) X₀.A (X₀.diag c₁) ψR)
    {D : R} (hD : D ≠ 0) {τ : E →+* K} {e f : Fin n → R}
    (he : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) τ = R ∙ e)
    (hf : f ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar τ))
    (hsup : ∀ h : Fin n → R, D • h ∈ ⨆ σ : E →+* K, GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) σ)
    (horth : ∀ σ σ' : E →+* K, σ' ≠ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar σ →
      ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) σ,
      ∀ y ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) σ',
      LinearMap.BilinForm.baseChange K (ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap : LinearMap.BilinForm R (Fin n → R)) x y = 0)
    {N : Module.End K (K ⊗[R] (Fin n → R))} {M : Module.End R (Fin n → R)}
    (hN : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsLower (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) τ e f N)
    (hM : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsScaledRestr D N M)
    (m : GrpMor (dp0 R) (𝟙 _) X₀.A (dp0 ℂ) (𝟙 _) X.A (algebraMap R ℂ) (spMap (algebraMap R ℂ)) p)
    {ψ : LinearMap.BilinForm ℂ (HdR X.A)} (hψ : ∀ x x' y y', m.Corr x x' → m.Corr y y' → ψ x' y' = algebraMap R ℂ (ψR x y))
    {ev yv : HdR X.A} (hev : m.Corr (eH.symm e) ev) (hyv : m.Corr (eH.symm f) yv) (h0 : ψ ev yv ≠ 0)
    (x₀ : HdR X₀.A) (x : HdR X.A) (hx : m.Corr x₀ x) :
    m.Corr (eH.symm.conjRingEquiv M x₀) ((((D : ℂ) / ψ ev yv) • (ψ.flip yv).smulRight yv) x) := by
  obtain ⟨k, t, hk, ht⟩ := GlobalTheory.RealMult.PolScale.exists_nat_mul_polForm_eq hDR (FR E) 𝔠 R X₀ c₁ c₀ hc₀ ψR _ hψR hψ₀
  have hact : act (dp0 R) (𝟙 _) X₀.rm t = act (dp0 R) (𝟙 _) cm (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF c t) := by
    haveI := X₀.rm.hom t
    haveI := cm.hom (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF c t)
    rw [act_apply, act_apply]
    exact push_congr _ _ (hrm t).symm
  have hγ := hψ _ _ _ _ hev hyv
  have h1 := lower_eq_of_scale (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm))
    (ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap) (ψR.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap) hD he hf hsup horth
    hN hM hk (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF c t) (fun x y ↦ by
      have := ht (eH.symm x) (eH.symm y)
      rw [hact] at this
      simpa using this) (fun h ↦ h0 (by
      have h' : ψR (eH.symm e) (eH.symm f) = 0 := h
      rw [hγ, h', map_zero])) (eH x₀)
  have h2 : ψR (eH.symm e) (eH.symm f) • eH.symm (M (eH x₀)) = (D * ψR x₀ (eH.symm f)) • eH.symm f := by
    have := congrArg eH.symm h1
    simpa using this
  intro z
  have h3 := congrArg (algebraMap R ℂ) (LinearMap.congr_fun h2 z)
  simp only [LinearMap.smul_apply, smul_eq_mul, map_mul] at h3
  have h4 : eH.symm.conjRingEquiv M x₀ = eH.symm (M (eH x₀)) := rfl
  rw [h4]
  simp only [LinearMap.smul_apply, LinearMap.smulRight_apply, LinearMap.flip_apply, smul_eq_mul]
  have h5 : ψ.flip yv x = algebraMap R ℂ (ψR x₀ (eH.symm f)) := hψ _ _ _ _ hx hyv
  rw [hyv z, h5, div_mul_eq_mul_div, div_eq_iff h0, hγ]
  have h6 : algebraMap R ℂ D = (D : ℂ) := rfl
  rw [h6] at h3
  linear_combination -h3

theorem neg_le_val_inv {R : Subring ℂ} [IsDiscreteValuationRing R] (l : ℕ) (x : R) (q : ℚ) (hx : x ≠ 0)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) x) ≤ (q : WithTop ℚ)) :
    ((-q : ℚ) : WithTop ℚ) ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l ((algebraMap R (FractionRing R) x)⁻¹) := by
  have hx' : algebraMap R (FractionRing R) x ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hx
  unfold GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp at h ⊢
  rw [if_neg hx'] at h
  rw [if_neg (inv_ne_zero hx')]
  have ho : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R ((algebraMap R (FractionRing R) x)⁻¹) = - GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R (algebraMap R (FractionRing R) x) := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw
    rw [map_inv₀, WithZero.log_inv, neg_neg]
  rw [ho]
  have h' := WithTop.coe_le_coe.1 h
  refine WithTop.coe_le_coe.2 ?_
  push_cast
  rw [neg_div]
  exact neg_le_neg h'

end GlobalTheory.LatModel.HalfLower
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarisedAbelianGenericFibreTraitUniformisStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polarisedAbelian_generic_fibre_trait_uniformised : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : GlobalTheory.UU.CP G), IsSemiAbelian G → UnifTrait D G P.L.L →
    ∃ (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A), IsMonHom gen.hom ∧
      LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) := by
  first | exact @GlobalTheory.Mum.TraitGeneric.exists_polAV_generic | exact GlobalTheory.Mum.TraitGeneric.exists_polAV_generic | (intros; apply GlobalTheory.Mum.TraitGeneric.exists_polAV_generic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarisedAbelianSemiAbelianSiegelPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.CExtGen

theorem exists_polAV_semiAbelian : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V],
    GlobalTheory.Mum.Base V → IsDiscreteValuationRing V → ∀ y : Sp (FractionRing V) ⟶ F.X,
      ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (f : V →+* V₁)
        (fK : FractionRing V →+* FractionRing V₁), GlobalTheory.LN.CDvr V₁ ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧
        (∀ a, fK (algebraMap V _ a) = algebraMap V₁ _ (f a)) ∧
        ∃ (A : PolAV (Sp (FractionRing V₁))) (α : A.A.left ⟶ F.univ.A.left) (α₂ : (G2 A.A).left ⟶ (G2 F.univ.A).left),
          IsGrpPullback A.A F.univ.A (spMap fK ≫ y) α ∧ IsSquare α α₂ ∧ LBIso (abelian₂ A.A A.L) (F.univ.P.pull α₂) ∧
          ∃ (G : Over (Sp V₁)) (_ : GrpObj G) (_ : IsCommMonObj G) (gen : (Over.pullback (jK V₁)).obj G ≅ A.A),
            IsSemiAbelian G ∧ IsMonHom gen.hom := by
  intro g n o _ ζ F V _ _ _ hB hV y
  have hC : GlobalTheory.LN.CDvr V := ⟨hV, hB.1.2.2.2, hB.2⟩
  haveI : CharZero V := hB.2
  haveI : CharZero (FractionRing V) := inferInstance
  obtain ⟨R₁, _, _, hfin, hnt, P, α, α₂, hα, hsq, hlam⟩ := GlobalTheory.T.exists_lambdaPolarisation_siegelObject_charZeroField g n o ζ F.X F.s F.univ F.princ (FractionRing V) y
  obtain ⟨W₁, _, _, _, f₁, ψ, hW₁, hi₁, hl₁, hf₁, hc₁⟩ := GlobalTheory.T.exists_completeDVR_finite_map_of_finiteAlgebra V hC R₁ hfin hnt
  obtain ⟨P₁, φ₁, hP₁, -, hL₁⟩ := GlobalTheory.KeyFam.SameLam.exists_polPB P ψ
  obtain ⟨β₂, hβ₂, hΛ₁⟩ := GlobalTheory.Mum.lbIso_lam_pull_of_isGrpPullback _ _ _ P.A P₁.A φ₁ hP₁
  have lam₁ := hΛ₁ P.L P₁.L _ F.univ.P α₂ P.isLB P₁.isLB F.univ.isLB hL₁ hlam
  obtain ⟨V₁, _, _, _, f₂, fK₂, hV₁, hi₂, hl₂, hf₂, hc₂, A, β, hβ, hLA, G, _, _, gen, hG, hgen⟩ := GlobalTheory.T.exists_semiAbelianModel_finiteExt_completeDVR W₁ hW₁ P₁
  obtain ⟨γ₂, hγ₂, hΛ₂⟩ := GlobalTheory.Mum.lbIso_lam_pull_of_isGrpPullback _ _ _ P₁.A A.A β hβ
  have lam₂ := hΛ₂ P₁.L A.L _ F.univ.P (β₂ ≫ α₂) P₁.isLB A.isLB F.univ.isLB hLA lam₁
  refine ⟨V₁, inferInstance, inferInstance, inferInstance, f₂.comp f₁, fK₂.comp (ψ.comp (algebraMap _ R₁)), hV₁,
    hi₂.comp hi₁, ?_, hf₂.comp hf₁, ?_, A, β ≫ φ₁ ≫ α, γ₂ ≫ β₂ ≫ α₂, ?_, ?_, ?_, G, inferInstance, inferInstance, gen, hG,
    hgen⟩
  · exact RingHom.isLocalHom_comp f₂ f₁
  · intro a
    simp [hc₁, hc₂]
  · refine (hβ.comp (hP₁.comp hα)).congr ?_ rfl
    simp [spMap, Spec.map_comp]
  · exact GlobalTheory.ZM.SiegPull.isSquare_comp hγ₂ (GlobalTheory.ZM.SiegPull.isSquare_comp hβ₂ hsq)
  · simpa [Category.assoc] using lam₂

end GlobalTheory.CExtGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosNonzeroPairSectionOfAmple
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

namespace GlobalTheory.HSNef

theorem exists_pos_nonzero_mem_H : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.A.B → ∀ (a : ℤ),
      ∃ (c : ℕ) (h : X.functionField), 0 < c ∧ h ≠ 0 ∧ h ∈ P.H a c := by
  intro k _ X _ p D hX P hA a
  obtain ⟨M, hM⟩ := GlobalTheory.T.exists_hermitianRepresentative_integerCombination k X p P a 0
  obtain ⟨b, hb, u, hu⟩ := exists_sec_finite_subset_nonzeroLocus k X p D hX M P.A hA {genericPoint X}
    (Set.finite_singleton _)
  have hA1 := (Pair.rep_base k X p P).2.1
  have hAb := Pair.rep_pow k X p P 0 1 P.A b hA1
  have hN := Pair.rep_tens k X p P a 0 _ _ M (P.A.pow b) hM hAb
  have e1 : a + (b : ℤ) * 0 = a := by ring
  have e2 : (0 : ℤ) + (b : ℤ) * 1 = b := by ring
  rw [e1, e2] at hN
  obtain ⟨e, -, hrange, -, hloc⟩ := RepDict.rep_dict k X p P a b _ hN
  have hmem : e u ∈ P.H a b := by
    have : e u ∈ Set.range e := Set.mem_range_self u
    rw [hrange] at this
    exact this
  obtain ⟨i, hi⟩ : ∃ i, genericPoint X ∈ P.L.B.U i :=
    Opens.mem_iSup.1 (P.L.isLB.cover.ge (Opens.mem_top _))
  obtain ⟨j, hj⟩ : ∃ j, genericPoint X ∈ P.A.B.U j :=
    Opens.mem_iSup.1 (P.A.isLB.cover.ge (Opens.mem_top _))
  have hU := (hloc u (genericPoint X) i j hi hj).1 (hu rfl)
  refine ⟨b, e u, hb, fun h0 => ?_, hmem⟩
  have hz : ∀ x : X, ¬ UnitAt x (0 : X.functionField) := by
    rintro x ⟨w, hw, h⟩
    exact (hw.map (algebraMap _ X.functionField)).ne_zero h
  rw [h0] at hU
  have z : P.loc a b 0 i j = 0 := by simp [Pair.loc]
  rw [z] at hU
  exact hz _ hU

end GlobalTheory.HSNef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeAboveValuationEqStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_above_valuation_eq : ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (𝔣 : Ideal (OF E)) (l : ℕ), l.Prime →
    ∃ P : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ P.asIdeal ∧ ((GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.cNum_vp 𝔣 l P : ℚ) : ℝ) = c_vp 𝔣 l := by
  first | exact @GlobalTheory.CNumAtPrime.cNum_eq_c_vp | exact GlobalTheory.CNumAtPrime.cNum_eq_c_vp | (intros; apply GlobalTheory.CNumAtPrime.cNum_eq_c_vp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorOverSourceOfBirationalStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open GlobalTheory.Discrepancy GlobalTheory.EtaleKlt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primeDivisor_over_source_of_birational : ∀ {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp ℂ) (s : Y ⟶ X) [IsDominant s],
    Function.Bijective (functionFieldMap s) → ∀ E : DivOver p, ∃ E' : DivOver (s ≫ p), DivOver.Over s E' E := by
  first | exact @GlobalTheory.Discrepancy.DivOver.exists_over_complex | exact GlobalTheory.Discrepancy.DivOver.exists_over_complex | (intros; apply GlobalTheory.Discrepancy.DivOver.exists_over_complex <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorOverTargetOfBirationalStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open GlobalTheory.Discrepancy GlobalTheory.EtaleKlt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primeDivisor_over_target_of_birational : ∀ {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp ℂ) (s : Y ⟶ X) [IsDominant s],
    Function.Bijective (functionFieldMap s) → ∀ E' : DivOver (s ≫ p), ∃ E : DivOver p, DivOver.Over s E' E := by
  first | exact @GlobalTheory.Discrepancy.DivOver.exists_over_of_bijective_complex | exact GlobalTheory.Discrepancy.DivOver.exists_over_of_bijective_complex | (intros; apply GlobalTheory.Discrepancy.DivOver.exists_over_of_bijective_complex <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimitiveLatticeMultiplierStatement
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primitive_lattice_multiplier : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (L : Set E)
    (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ L 0 X),
    ∃ b : E, (∀ x ∈ L, b * x ∈ L) ∧ IntermediateField.adjoin ℚ {b} = ⊤ := by
  first | exact @GlobalTheory.OrderPrimitive.exists_primitive_mul_mem | exact GlobalTheory.OrderPrimitive.exists_primitive_mul_mem | (intros; apply GlobalTheory.OrderPrimitive.exists_primitive_mul_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipalPolarisationGenericFibreTwoTorsioStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_principal_polarisation_genericFibre_twoTorsion_translate : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → ∀ P : GlobalTheory.UU.CP G, LBIso P.L.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → ∃ (A₂ : PolAV (Sp (FractionRing R))) (gen₂ : (Over.pullback (jK R)).obj G ≅ A₂.A), IsMonHom gen₂.hom ∧ LBIso (A₂.L.pull gen₂.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) := by
  first | exact @GlobalTheory.TwistAV.exists_translate_pol | exact GlobalTheory.TwistAV.exists_translate_pol | (intros; apply GlobalTheory.TwistAV.exists_translate_pol <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullDegIdentitySelfAdmissible
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.DegPullId

theorem exists_isPullDeg_id_self : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I),
    ∃ h : IsPullDeg (RingHom.id R) D.toPre D.toPre, (∀ x, h.xe x = x) ∧
      h.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) = 𝟙 _ := by
  intro R _ _ I hR D
  have : IsMonHom (Iso.refl D.toPre.P.A).hom := inferInstanceAs (IsMonHom (𝟙 D.toPre.P.A))
  have gp : IsGrpPullback D.toPre.P.A D.toPre.P.A (specOf (RingHom.id R)) (Iso.refl D.toPre.P.A).hom.left :=
    (isGrpPullback_of_iso (Iso.refl D.toPre.P.A)).congr (specOf_id R).symm rfl
  obtain ⟨e, me, hF⟩ := grpPullback_iso gp (isGrpPullback_pullback D.toPre.P.A (specOf (RingHom.id R)))
  have hF' : e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) = 𝟙 _ := hF
  obtain ⟨W, hW, ⟨ψW⟩⟩ := psiOnExists R I hR D
  obtain ⟨hD, h₁, -, h₃⟩ := UnifUniq.exists_isPullDeg_id D.toPre D.toPre W hW ψW e me
    (isoPullId (Geo.Tor.idIso D.toPre.P.L) hF') ((isGen_iff _).2 (isoPullId_pgen (idIso_isGen D.toPre.P.isLB) hF'))
    ((congrArg (_ ≫ ·) hF').trans (Category.comp_id _))
    (NoTorus.pmaps_id hF' (K := PUnit) (fun _ => eSec D.toPre.P.A) (fun _ => 1) D.toPre.rig_gen) (AddEquiv.refl _)
    (fun x => (congrArg (_ ≫ ·) hF').trans (Category.comp_id _))
    (fun x => NoTorus.pmaps_id hF' (K := PUnit) (fun _ => D.toPre.xK x) (fun _ => -1) (D.toPre.psi_gen x))
  refine ⟨hD, fun x => ?_, ?_⟩
  · rw [h₃]; rfl
  · rw [h₁]; exact hF'

end GlobalTheory.DegPullId
end
end


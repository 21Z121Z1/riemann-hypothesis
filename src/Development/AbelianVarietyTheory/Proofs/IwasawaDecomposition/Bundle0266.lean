import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1020
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0255
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0006
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocAutHodgeTateWeightsLevelZeroDef
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0140
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0252
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0143
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0132
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0151
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExtUHInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0256
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0226
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothVectorsModerateGrowthSmoothFrechetRep

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntersectionNumberEqGenericRankMulProjCurve
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory.VB

section Generic

variable {X : Scheme.{0}} [IsIntegral X]

theorem genRank_twist {F : X.Modules} {M : LB X} (hM : M.IsLB) :
    genRank (twist F M) = genRank F :=
  have ⟨e⟩ := Twist.nonempty_stalkEquiv (F := F) hM (genericPoint X)
  e.finrank_eq

theorem exists_germ_ne_zero {F : X.Modules} (h : QCoh.IsGloballyGenerated F)
    (hr : genRank F ≠ 0) :
    ∃ s : Γ(F, ⊤), F.presheaf.germ ⊤ (genericPoint X) trivial s ≠ 0 := by
  obtain ⟨n, s, hs⟩ := QCoh.isGloballyGenerated_iff_spanStalks.1 h
  by_contra! H
  have : Subsingleton (genStalk F) := subsingleton_of_forall_eq 0 fun t => by
    have ht := (hs (genericPoint X)).ge (Submodule.mem_top (x := t))
    have e : (Set.range fun i => ((F.presheaf.germ ⊤ (genericPoint X) trivial (s i) :
        (F.presheaf.stalk (genericPoint X) :)))) ⊆ {0} := by
      rintro _ ⟨i, rfl⟩
      exact H _
    simpa using Submodule.span_mono e ht
  exact hr Module.finrank_zero_of_subsingleton

theorem mono_sectionHom {F : X.Modules} (s : Γ(F, ⊤))
    (hs : F.presheaf.germ ⊤ (genericPoint X) trivial s ≠ 0) : Mono (QCoh.sectionHom s) := by
  refine QCoh.mono_of_locally_app_injective _ fun W x hx => ⟨W, hx, le_rfl, fun a b e => ?_⟩
  have hη := genericPoint_mem hx
  apply (QCoh.structureModuleSectionsEquiv W).injective
  have e' : (QCoh.structureModuleSectionsEquiv W a - QCoh.structureModuleSectionsEquiv W b) •
      Twist.resM F (le_top : W ≤ ⊤) s = 0 := by
    rw [sub_smul, sub_eq_zero]
    exact e
  have e'' := congrArg (F.presheaf.germ W _ hη) e'
  rw [QCoh.germ_smul, Twist.germ_resM, map_zero] at e''
  have := (smul_eq_zero.1 e'').resolve_right hs
  exact sub_eq_zero.1 (germ_injective_of_isIntegral X _ hη (this.trans (map_zero _).symm))

end Generic

variable {κ : Type} [Field κ] {Z : Scheme.{0}} [IsIntegral Z] [Algebra κ Γ(Z, ⊤)]

theorem interNum_one_of_genRank_eq (hp : IsProjOver (strHom κ Z)) (hd : topologicalKrullDim Z = 1)
    {N : LB Z} (hN : N.IsLB) (r : ℕ) :
    ∀ (G : Z.Modules) [QCoh.IsFiniteQC G], genRank G = r →
      interNum κ G ![N] = r * interNum κ (structureModule Z) ![N] := by
  have hf := algebraMap_eq_strHom κ Z
  have hL := isLB_vecOne hN
  have h1 : ∀ {F : Z.Modules} [QCoh.IsFiniteQC F], FiniteCohTwists κ F :=
    fun {F} _ => finiteCohTwists_of_isProjOver hf F hp
  obtain ⟨_, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hp
  induction r with
  | zero =>
    intro G _ h
    have h0 : QCoh.suppDim G ≤ 0 := suppDim_le_zero hd h
    have : QCoh.suppDim G < Fintype.card (Fin 1) := h0.trans_lt (by simp)
    rw [interNum_eq_zero_of_isProjOver hf G hp this hL]
    simp
  | succ r ih =>
    intro G _ h
    obtain ⟨n, hn⟩ := (hA.eventually_isGloballyGenerated_twist G).exists
    have hM := isLB_lbPow hA.isLB n
    have := Twist.isFiniteQC_twist (F := G) hM
    have hr : genRank (twist G (lbPow A n)) = r + 1 := (genRank_twist hM).trans h
    obtain ⟨s, hs⟩ := exists_germ_ne_zero hn (by omega)
    have := mono_sectionHom s hs
    have e₁ : interNum κ (twist G (lbPow A n)) ![N] = interNum κ G ![N] :=
      (diffVanish_chiPic_of_isProjOver (d := 1) hf G hp
        ((QCoh.suppDim_le G).trans_eq (by rw [hd]; rfl))).interNum_twist (by simp) hL hM
    have e₂ := interNum_cokernel (k := κ) (QCoh.sectionHom s) hL h1 h1
    have e₃ := genRank_cokernel (QCoh.sectionHom s)
    rw [(isVB_structureModule Z).genRank_eq, hr] at e₃
    rw [ih _ (by omega)] at e₂
    push_cast
    linarith

theorem interNum_one_eq_genRank_mul : ∀ (κ : Type) [Field κ] (Z : Scheme.{0}) [IsIntegral Z]
    [Algebra κ Γ(Z, ⊤)], IsProjOver (strHom κ Z) → topologicalKrullDim Z = 1 →
    ∀ (G : Z.Modules) [GlobalTheory.QCoh.IsFiniteQC G] (N : LB Z), N.IsLB →
      interNum κ G ![N] = (GlobalTheory.VB.genRank G : ℤ) * interNum κ (structureModule Z) ![N] :=
  fun _ _ _ _ _ hp hd G _ _ hN => interNum_one_of_genRank_eq hp hd hN _ G rfl

end GlobalTheory.VB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagRefinementBundleComp
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

variable {ι : Type} {m : ι → ℕ}

theorem mat_chain {K₁ K₂ K₃ : Type} [Field K₁] [Field K₂] [Field K₃] (ψ : K₁ →+* K₂) (ψ' : K₂ →+* K₃)
    (A'' : Mat m K₃) (A' : Mat m K₂) (A : Mat m K₁) (hA' : ∀ τ, (A' τ).det ≠ 0) :
    A'' * (A'.map ψ')⁻¹ * (A' * (A.map ψ)⁻¹).map ψ' = A'' * (A.map (ψ'.comp ψ))⁻¹ := by
  rw [Mat.map_mul, Mat.map_inv, mul_assoc, ← mul_assoc (A'.map ψ')⁻¹,
    Mat.inv_mul (fun τ => by rw [Mat.det_map]; exact (map_ne_zero ψ').2 (hA' τ)), one_mul]
  congr 2

def valAt {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) {K : Type} [Field K]
    (q : Sp K ⟶ M.Z) : (M.O (q (IsLocalRing.closedPoint K))).toSubring →+* K :=
  RatModel.valHom q _ (RatModel.range_eq_singleton q (IsLocalRing.closedPoint K))

theorem valAt_apply {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) {K : Type} [Field K]
    (q : Sp K ⟶ M.Z) (x : (M.O (q (IsLocalRing.closedPoint K))).toSubring) : M.val q x = valAt M q x := rfl

end GlobalTheory.FlagBundle

namespace GlobalTheory.FlagBundle

variable {ι : Type} {m : ι → ℕ} {F : Type} [Field F] {Ω Ω' Ω'' : Type} [Field Ω] [Algebra F Ω] [Field Ω']
  [Algebra F Ω'] [Field Ω''] [Algebra F Ω'']

theorem val_chain {M' : RatModel F Ω'} {M'' : RatModel F Ω''} {φ : Ω →ₐ[F] Ω'}
    {φ' : Ω' →ₐ[F] Ω''} {f' : M''.Z ⟶ M'.Z} (hf' : M'.IsHom M'' φ' f') {K : Type} [Field K] (q : Sp K ⟶ M''.Z)
    {k k' : ι → ℕ} {A'' : Mat m Ω''} {A' : Mat m Ω'} {A : Mat m Ω} (hA' : ∀ τ, (A' τ).det ≠ 0)
    (h2 : Par k' (M''.O (q (IsLocalRing.closedPoint K))).toSubring (A'' * (A'.map φ')⁻¹))
    (h1 : Par k (M'.O (f' (q (IsLocalRing.closedPoint K)))).toSubring (A' * (A.map φ)⁻¹)) :
    (A'' * (A.map (φ'.comp φ))⁻¹).map (M''.val q) =
      (A'' * (A'.map φ')⁻¹).map (M''.val q) * (A' * (A.map φ)⁻¹).map (M'.val (q ≫ f')) := by
  have h1' : Par k (M''.O (q (IsLocalRing.closedPoint K))).toSubring ((A' * (A.map φ)⁻¹).map φ') :=
    h1.map (φ' : Ω' →+* Ω'') fun x hx => hf'.map_mem_O hx
  have e := mat_chain (φ : Ω →+* Ω') (φ' : Ω' →+* Ω'') A'' A' A hA'
  have e2 : (A'' * (A.map (φ'.comp φ))⁻¹) = A'' * (A'.map φ')⁻¹ * (A' * (A.map φ)⁻¹).map φ' := e.symm
  rw [e2, Par.map_mul_of h2 h1' (M''.val q) (valAt M'' q) (valAt_apply M'' q)]
  congr 1
  funext τ
  ext i j
  show M''.val q (φ' ((A' * (A.map φ)⁻¹) τ i j)) = M'.val (q ≫ f') ((A' * (A.map φ)⁻¹) τ i j)
  exact (hf'.val_comp q (IsLocalRing.closedPoint K) ((h1 τ).1 i j)).symm

theorem Refines.comp {M : RatModel F Ω} {M' : RatModel F Ω'} {M'' : RatModel F Ω''} {φ : Ω →ₐ[F] Ω'}
    {f : M'.Z ⟶ M.Z} {φ' : Ω' →ₐ[F] Ω''} {f' : M''.Z ⟶ M'.Z} {k k' k'' : ι → ℕ} {S : Fr M m k}
    {S' : Fr M' m k'} {S'' : Fr M'' m k''} (h1 : Refines S S' φ f) (h2 : Refines S' S'' φ' f') :
    Refines S S'' (φ'.comp φ) (f' ≫ f) where
  le := le_trans h1.le h2.le
  hom := h1.hom.comp h2.hom
  sub z'' A'' hA'' A hA := by
    obtain ⟨A', hA'⟩ := S'.nonempty (f' z'')
    have e : A'' * (A.map (φ'.comp φ))⁻¹ = A'' * (A'.map φ')⁻¹ * (A' * (A.map φ)⁻¹).map φ' :=
      (mat_chain (φ : Ω →+* Ω') (φ' : Ω' →+* Ω'') A'' A' A (Fr.det_ne hA')).symm
    rw [e]
    exact ((h2.sub z'' A'' hA'' A' hA').mono h1.le le_rfl).mul
      ((h1.sub (f' z'') A' hA' A hA).map (φ' : Ω' →+* Ω'') fun x hx => h2.hom.map_mem_O hx)
  rad z'' g hg := h2.rad z'' (φ g) (h1.rad (f' z'') g hg)
  lifts K _ x A hA h hh := by
    obtain ⟨p', ⟨hp'x, A', hA', hP'⟩, hu1⟩ := h1.lifts K x A hA h hh
    obtain ⟨p'', ⟨hp'', A'', hA'', hP''⟩, hu2⟩ :=
      h2.lifts K p' A' hA' (h * ((A' * (A.map φ)⁻¹).map (M'.val p'))⁻¹) hP'
    have hAx : A ∈ S.S (f (p' (IsLocalRing.closedPoint K))) := by
      have h0 := hA; rw [← hp'x] at h0; exact h0
    have fac : ∀ q : Sp K ⟶ M''.Z, q ≫ f' = p' → ∀ B'' ∈ S''.S (q (IsLocalRing.closedPoint K)),
        (B'' * (A.map (φ'.comp φ))⁻¹).map (M''.val q) =
          (B'' * (A'.map φ')⁻¹).map (M''.val q) * (A' * (A.map φ)⁻¹).map (M'.val p') := by
      intro q hq B'' hB''
      have hq' : p' (IsLocalRing.closedPoint K) = f' (q (IsLocalRing.closedPoint K)) := by
        rw [← hq]; rfl
      have hA'q : A' ∈ S'.S (f' (q (IsLocalRing.closedPoint K))) := by rw [← hq']; exact hA'
      have hAq : A ∈ S.S (f (f' (q (IsLocalRing.closedPoint K)))) := by rw [← hq']; exact hAx
      rw [val_chain h2.hom q (Fr.det_ne hA') (h2.sub _ B'' hB'' A' hA'q) (h1.sub _ A' hA'q A hAq), hq]
    refine ⟨p'', ⟨by rw [← Category.assoc, hp'', hp'x], A'', hA'', ?_⟩, ?_⟩
    · rw [fac p'' hp'' A'' hA'', Mat.mul_inv_rev, ← mul_assoc]
      exact hP''
    · rintro q ⟨hqx, B'', hB'', hPq⟩
      have hq1 : q ≫ f' = p' := by
        refine hu1 (q ≫ f') ⟨by rw [Category.assoc, hqx], ?_⟩
        obtain ⟨A₁, hA₁⟩ := S'.nonempty ((q ≫ f') (IsLocalRing.closedPoint K))
        refine ⟨A₁, hA₁, ?_⟩
        have hA₁' : A₁ ∈ S'.S (f' (q (IsLocalRing.closedPoint K))) := hA₁
        have hAq : A ∈ S.S (f (f' (q (IsLocalRing.closedPoint K)))) := by
          have h0 := hA; rw [← hqx] at h0; exact h0
        have h2s := h2.sub _ B'' hB'' A₁ hA₁'
        rw [val_chain h2.hom q (Fr.det_ne hA₁') h2s (h1.sub _ A₁ hA₁' A hAq)] at hPq
        have hG : Par k' ⊤ ((B'' * (A₁.map φ')⁻¹).map (M''.val q)) :=
          h2s.map_of _ (valAt M'' q) (valAt_apply M'' q)
        have e : h * ((A₁ * (A.map φ)⁻¹).map (M'.val (q ≫ f')))⁻¹ =
            h * ((B'' * (A₁.map φ')⁻¹).map (M''.val q) * (A₁ * (A.map φ)⁻¹).map (M'.val (q ≫ f')))⁻¹ *
              (B'' * (A₁.map φ')⁻¹).map (M''.val q) := by
          rw [Mat.mul_inv_rev, mul_assoc, mul_assoc, Mat.inv_mul hG.det_ne, mul_one]
        rw [e]
        exact (hPq.mono h2.le le_rfl).mul hG
      refine hu2 q ⟨hq1, B'', hB'', ?_⟩
      rw [fac q hq1 B'' hB'', Mat.mul_inv_rev, ← mul_assoc] at hPq
      exact hPq

end GlobalTheory.FlagBundle

theorem GlobalTheory.FlagBundle.refines_comp : ∀ (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω'] (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (Ω'' : Type) [Field Ω''] [Algebra F Ω''] (M'' : RatModel F Ω'') (φ' : Ω' →ₐ[F] Ω'') (f' : M''.Z ⟶ M'.Z) (ι : Type) (m k k' k'' : ι → ℕ) (S : Fr M m k) (S' : Fr M' m k') (S'' : Fr M'' m k''), Refines S S' φ f → Refines S' S'' φ' f' → Refines S S'' (φ'.comp φ) (f' ≫ f) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 => h1.comp h2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHermitianJmBracket
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum

theorem isHermitian_Jm_bracket {n : ℕ} (ε : Fin n → Bool) : (Jm ε).IsHermitian := by
  unfold Jm
  refine Matrix.isHermitian_diagonal_of_self_adjoint _ ?_
  funext i
  simp only [Pi.star_apply]
  split_ifs <;> simp

theorem dRep_bracket : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ w, Sm ε σ w → ∀ X ∈ lieSet ε, ∀ Y ∈ lieSet ε, dRep σ X (dRep σ Y w) - dRep σ Y (dRep σ X w) = dRep σ (X * Y - Y * X) w := by
  intro n ε H _ _ _ σ h w hw X hX Y hY
  have hd : (Jm ε).det ≠ 0 := ((isUnit_iff_isUnit_det _).1 (isUnit_Jm ε)).ne_zero
  have key := fun v (hv : Sm ε σ v) =>
    GlobalTheory.HolDict.LieAct.main n (Jm ε) H σ (isHermitian_Jm_bracket ε) hd h.1 v v hv hv
  have hB : X * Y - Y * X ∈ lieSet ε := by
    have h1 : Xᴴ * Jm ε = -(Jm ε * X) := eq_neg_of_add_eq_zero_left hX
    have h2 : Yᴴ * Jm ε = -(Jm ε * Y) := eq_neg_of_add_eq_zero_left hY
    show (X * Y - Y * X)ᴴ * Jm ε + Jm ε * (X * Y - Y * X) = 0
    rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, sub_mul, mul_assoc, mul_assoc, h1, h2,
      mul_neg, mul_neg, ← mul_assoc, ← mul_assoc, h1, h2]
    noncomm_ring
  have hXw : Sm ε σ (dRep σ X w) := dRep_mem (isUnit_Jm ε) h.1 hw hX
  have hYw : Sm ε σ (dRep σ Y w) := dRep_mem (isUnit_Jm ε) h.1 hw hY
  have e := ((key w hw).1 0 X Y).2.2
  rw [(key w hw).2.1 _ hB, (key w hw).2.1 X hX, (key w hw).2.1 Y hY, (key _ hXw).2.1 Y hY,
    (key _ hYw).2.1 X hX] at e
  exact e.symm

end GlobalTheory.TypeSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIsoOfBijectiveGeomPointsSmoothProjCharZeroStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ProjVar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIso_of_bijective_geomPoints_smoothProj_charZero : ∀ (F : Type) [Field F] [CharZero F] (Y₁ Y₂ : Var F) (h : Y₁.X ⟶ Y₂.X), h ≫ Y₂.str = Y₁.str → (∀ (K : Type) [Field K] [IsAlgClosed K], Function.Bijective (fun p : Sp K ⟶ Y₁.X => p ≫ h)) → IsIso h := by
  first | exact @GlobalTheory.BijPointsIso.isIso_of_bijective_points | exact GlobalTheory.BijPointsIso.isIso_of_bijective_points | (intros; apply GlobalTheory.BijPointsIso.isIso_of_bijective_points <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerMapRep
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting

theorem ss_exists : ∀ {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k), ∃ ρ' : Γ →* GL (Fin a) k, IsSSRep ρ' ∧ ρ.ker ≤ ρ'.ker ∧ ∀ g, (ρ' g : Matrix (Fin a) (Fin a) k).charpoly = (ρ g : Matrix (Fin a) (Fin a) k).charpoly := GlobalTheory.T.exists_semisimplification_matrix_rep_same_charpoly

theorem indep : ∀ (D : D7) (Rw : RowSide D) (Pl : PlSide D) (X : LocNd (lay0 D)) (Y : LocAut X), GlobalTheory.RowTie.ChebSplit D.nd → (∀ i σ w, Y.locW i σ w = Rw.locR σ w) → (∀ (i : X.nd.Loc) (y : X.nd.O i), ∃ h : iotaO X.nd Y.naut i y ∈ Pl.plB (X.nd.w i), fbCast (X.nd.w_l i) (D.what₂.places.resChar_prime (X.nd.w i)) (X.nd.lPrime i).out (Pl.plκ (X.nd.w i) (IsLocalRing.residue (Pl.plB (X.nd.w i)) ⟨_, h⟩)) = Y.naut.kFbar i (IsLocalRing.residue (X.nd.O i) y)) → ∀ (σ : D.what₂.FT) (i i' : X.nd.Loc), X.nd.w i = X.nd.w i' → ∀ (Sig Sig' : List (Formalism.BasicNotions.Part Y.naut.CG)) (ρ : G D.host.E X.nd.Om →* GL (Fin D.R.r) (X.nd.O i)) (ρ' : G D.host.E X.nd.Om →* GL (Fin D.R.r) (X.nd.O i')), HasParamW X.nd Y.naut i σ Sig → IsRepOfSig X.nd Y.naut i Sig ρ → HasParamW X.nd Y.naut i' σ Sig' → IsRepOfSig X.nd Y.naut i' Sig' ρ' → ∀ (g : G D.host.E X.nd.Om) (n : ℕ), iotaO X.nd Y.naut i ((ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i)).charpoly.coeff n) - iotaO X.nd Y.naut i' ((ρ' g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i')).charpoly.coeff n) ∈ (Pl.plB (X.nd.w i)).nonunits := GlobalTheory.T.charpoly_coeff_congr_same_place_alt

theorem ssRep_spec {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) :
    IsSSRep (ssRep ρ) ∧ ρ.ker ≤ (ssRep ρ).ker ∧
    ∀ g, (ssRep ρ g : Matrix (Fin a) (Fin a) k).charpoly = (ρ g : Matrix (Fin a) (Fin a) k).charpoly :=
  Classical.epsilon_spec (ss_exists ρ)

theorem castMt_eq {D : D7} {μ μ' : D.what₂.Tup} {j j' : ℕ} (h1 : μ = μ') (h2 : j = j') (M : Submodule ℂ (D.what₂.Mt μ j))
    (M' : Submodule ℂ (D.what₂.Mt μ' j')) (h : HEq M M') : castMt h1 h2 M = M' := by
  subst h1; subst h2; exact eq_of_heq h

theorem isOpen_ker_mapRep {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {O : Type} [CommRing O]
    [TopologicalSpace O] [IsTopologicalRing O] (I : Ideal O) (hI : IsOpen (I : Set O)) {k : Type} [CommRing k] (φ : O →+* k)
    (hφ : I ≤ RingHom.ker φ) {a : ℕ} (ρ : Γ →* GL (Fin a) O)
    (hρ : Continuous fun g => (ρ g : Matrix (Fin a) (Fin a) O)) :
    IsOpen ((mapRep φ ρ).ker : Set Γ) := by
  let U : Set Γ := ⋂ i : Fin a, ⋂ j : Fin a, (fun g => (ρ g : Matrix (Fin a) (Fin a) O) i j - (1 : Matrix (Fin a) (Fin a) O) i j) ⁻¹' (I : Set O)
  have hU : IsOpen U := by
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hI.preimage ?_
    exact ((continuous_apply j).comp ((continuous_apply i).comp hρ)).sub continuous_const
  have h1 : (1 : Γ) ∈ U := by
    simp only [U, Set.mem_iInter, Set.mem_preimage, map_one, Units.val_one, sub_self]
    intro i j; exact I.zero_mem
  have hsub : U ⊆ ((mapRep φ ρ).ker : Set Γ) := by
    intro g hg
    simp only [U, Set.mem_iInter, Set.mem_preimage] at hg
    show mapRep φ ρ g = 1
    apply Units.ext
    ext i j
    have := hφ (hg i j)
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at this
    simp only [mapRep, MonoidHom.coe_comp, Function.comp_apply, Units.coe_map, MonoidHom.coe_coe,
      RingHom.mapMatrix_apply, Matrix.map_apply, Units.val_one]
    change φ ((ρ g : Matrix (Fin a) (Fin a) O) i j) = (1 : Matrix (Fin a) (Fin a) k) i j
    rw [this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  exact Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hU.mem_nhds h1) hsub)

theorem isSSRep_one {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} : IsSSRep (1 : Γ →* GL (Fin a) k) := by
  intro W _
  obtain ⟨W', hW'⟩ := Submodule.exists_isCompl W
  exact ⟨W', fun g v hv => by simpa using hv, hW'⟩

theorem fbCast_trans {p q r : ℕ} (h1 : p = q) (h2 : q = r) (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (x : Fb p hp) :
    fbCast h2 hq hr (fbCast h1 hp hq x) = fbCast (h1.trans h2) hp hr x := by
  subst h1; subst h2; rfl

theorem plκ_cast (D : D7) (Pl : PlSide D) {lam lam' : D.what₂.places.Pl} (h : lam = lam') {p : ℕ} (hp : p.Prime)
    (h1 : D.what₂.places.resChar lam = p) (h1' : D.what₂.places.resChar lam' = p) (z z' : ℂ) (hz : z ∈ Pl.plB lam)
    (hz' : z' ∈ Pl.plB lam') (hd : z - z' ∈ (Pl.plB lam).nonunits) :
    fbCast h1 (D.what₂.places.resChar_prime lam) hp (Pl.plκ lam (IsLocalRing.residue (Pl.plB lam) ⟨z, hz⟩)) =
      fbCast h1' (D.what₂.places.resChar_prime lam') hp (Pl.plκ lam' (IsLocalRing.residue (Pl.plB lam') ⟨z', hz'⟩)) := by
  subst h
  have : IsLocalRing.residue (Pl.plB lam) ⟨z, hz⟩ = IsLocalRing.residue (Pl.plB lam) ⟨z', hz'⟩ := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
    rw [ValuationSubring.mem_nonunits_iff] at hd
    simpa using hd
  rw [this]

theorem charpoly_mapRep {Γ : Type} [Group Γ] {A B : Type} [CommRing A] [CommRing B] {a : ℕ} (f : A →+* B)
    (ρ : Γ →* GL (Fin a) A) (g : Γ) :
    ((mapRep f ρ g : GL (Fin a) B) : Matrix (Fin a) (Fin a) B).charpoly = (ρ g : Matrix (Fin a) (Fin a) A).charpoly.map f := by
  rw [← Matrix.charpoly_map]
  rfl

theorem isSSRep_rbarOf {D : D7} {X : LocNd (lay0 D)} (Y : LocAut X) (σ : D.what₂.FT) (lam : D.what₂.places.Pl) :
    IsSSRep (rbarOf Y σ lam) := by
  unfold rbarOf
  split_ifs with h
  · exact (ssRep_spec _).1
  · exact isSSRep_one

set_option maxHeartbeats 1000000 in
theorem rbar_tie_at (D : D7) (Rw : RowSide D) (Pl : PlSide D) (X : LocNd (lay0 D)) (Y : LocAut X)
    (hCheb : GlobalTheory.RowTie.ChebSplit D.nd) (hloc : ∀ i σ w, Y.locW i σ w = Rw.locR σ w)
    (hplB : ∀ (i : X.nd.Loc) (y : X.nd.O i), ∃ h : iotaO X.nd Y.naut i y ∈ Pl.plB (X.nd.w i), fbCast (X.nd.w_l i) (D.what₂.places.resChar_prime (X.nd.w i)) (X.nd.lPrime i).out (Pl.plκ (X.nd.w i) (IsLocalRing.residue (Pl.plB (X.nd.w i)) ⟨_, h⟩)) = Y.naut.kFbar i (IsLocalRing.residue (X.nd.O i) y))
    (i : X.nd.Loc) (σ : D.what₂.FT) (Sig : List (Formalism.BasicNotions.Part Y.naut.CG))
    (ρ : G D.host.E X.nd.Om →* GL (Fin D.R.r) (X.nd.O i)) (hP : HasParamW X.nd Y.naut i σ Sig)
    (hR : IsRepOfSig X.nd Y.naut i Sig ρ) (g : G D.host.E X.nd.Om) :
    ((rbarOf Y σ (X.nd.w i) g : Matrix (Fin D.R.r) (Fin D.R.r) _).charpoly).map
        (fbCast (X.nd.w_l i) (D.what₂.places.resChar_prime (X.nd.w i)) (X.nd.lPrime i).out).toRingHom =
      (ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i)).charpoly.map ((Y.naut.kFbar i).comp (IsLocalRing.residue (X.nd.O i))) := by
  have hex : RbarData Y σ (X.nd.w i) := ⟨i, rfl, Sig, ρ, hP, hR⟩
  unfold rbarOf
  rw [dif_pos hex, (ssRep_spec _).2.2 g, charpoly_mapRep, Polynomial.map_map]
  have hw0 := hex.choose_spec.1
  have hs := hex.choose_spec.2.choose_spec.choose_spec
  generalize hex.choose_spec.2.choose_spec.choose = ρ0 at hs ⊢
  generalize hex.choose_spec.2.choose = Sig0 at hs ρ0 ⊢
  ext n
  rw [Polynomial.coeff_map, Polynomial.coeff_map]
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  obtain ⟨hz0, e0⟩ := hplB hex.choose ((ρ0 g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O hex.choose)).charpoly.coeff n)
  obtain ⟨hz, e⟩ := hplB i ((ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i)).charpoly.coeff n)
  rw [← e0, ← e, fbCast_trans, fbCast_trans]
  exact plκ_cast D Pl hw0 _ _ _ _ _ hz0 hz
    (indep D Rw Pl X Y hCheb hloc hplB σ _ i hw0 Sig0 Sig ρ0 ρ hs.1 hs.2 hP hR g n)

set_option maxHeartbeats 1000000 in

theorem locTy_exists : ∀ (D : D7) (Rw : RowSide D) (Pl : PlSide D) (X : LocNd (lay0 D)) (Y : LocAut X), BlocksUnique D → GlobalTheory.RowTie.ChebSplit D.nd → (∀ i σ w, Y.locW i σ w = Rw.locR σ w) → (∀ i : X.nd.Loc, Y.naut.iotaQC i = qCast (X.nd.w_l i) (Pl.ι (X.nd.w i))) → (∀ (i : X.nd.Loc) (y : X.nd.O i), ∃ h : iotaO X.nd Y.naut i y ∈ Pl.plB (X.nd.w i), fbCast (X.nd.w_l i) (D.what₂.places.resChar_prime (X.nd.w i)) (X.nd.lPrime i).out (Pl.plκ (X.nd.w i) (IsLocalRing.residue (Pl.plB (X.nd.w i)) ⟨_, h⟩)) = Y.naut.kFbar i (IsLocalRing.residue (X.nd.O i) y)) → (∀ i k v, X.nd.gam0 i (D.naut.plGw k v) = D.ntypes.tg k v) → (∀ (i : X.nd.Loc) k v, X.nd.l i ≠ D.host.g k → haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; ∃ u : (ZMod (D.host.g k))ˣ, (u = D.nd.chiT k v ⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩ ∨ u = (D.nd.chiT k v ⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩)⁻¹) ∧ iotaO X.nd Y.naut i ((X.nd.chi i 1 (D.ntypes.tg k v) : (X.nd.O i)ˣ) : X.nd.O i) = D.ntypes.teichC k (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (u : ZMod (D.host.g k)))) → (∀ (i i' : X.nd.Loc) (σ' : (lay0 D).ntypes.Par), X.nd.mu i = X.nd.mu i' → X.nd.j i = X.nd.j i' → HEq (⨆ P ∈ {P | ∃ Sig, (∀ w, isoLoc X.nd Y.naut Sig w = (lay0 D).ntypes.locPar σ' w) ∧ IsBCV X.nd Y.naut i P (twistIso X.nd Y.naut (Sig ++ [muPart X.nd Y.naut i]) Y.naut.etaTinv)}, Y.naut.typeV i P) (⨆ P ∈ {P | ∃ Sig, (∀ w, isoLoc X.nd Y.naut Sig w = (lay0 D).ntypes.locPar σ' w) ∧ IsBCV X.nd Y.naut i' P (twistIso X.nd Y.naut (Sig ++ [muPart X.nd Y.naut i']) Y.naut.etaTinv)}, Y.naut.typeV i' P)) → ∃ Z : LocTy Y, BcTie X.nd Y.naut Z.ntypes ∧ RbarTie X.nd Y.naut Z.ntypes ∧ MtParTie X.nd Y.naut Z.ntypes ∧ ∀ σ lam, IsSSRep (Z.rbar σ lam) := by
  intro D Rw Pl X Y hBU hCheb hloc hiota hplB hgam hchi hMt
  refine ⟨{ bc := bcOf D Rw, bc_pos := ?_, bc_sum := ?_, rbar := rbarOf Y, rbar_open := ?_, heckeLoc_gamma_places := hgam, chiT_tg := ?_, MtPar := mtParOf Y }, ?_, ?_, ?_, ?_⟩
  · intro σ p hp
    unfold bcOf at hp
    split_ifs at hp with h
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 (Multiset.mem_coe.1 hp)
      obtain ⟨h1, h2, -⟩ := h.choose_spec.1 q hq
      exact ⟨h1, h2⟩
    · rw [Multiset.mem_singleton] at hp; subst hp
      refine ⟨?_, Nat.one_pos⟩
      have := D.R.m_add_three_le_k; have := D.R.two_le_m
      simp only [Ranks.r]; omega
  · intro σ
    unfold bcOf
    split_ifs with h
    · have := h.choose_spec.2.1
      simp only [Multiset.map_coe, Multiset.sum_coe, List.map_map]
      simpa [rankIso, Function.comp_def] using this
    · simp
  · intro σ lam
    show IsOpen (((rbarOf Y σ lam).ker : Subgroup _) : Set (G D.host.E X.nd.Om))
    unfold rbarOf
    split_ifs with h
    · apply Subgroup.isOpen_mono (ssRep_spec _).2.1
      have hc := h.choose_spec.2.choose_spec.choose_spec.2.1
      refine isOpen_ker_mapRep (IsLocalRing.maximalIdeal (X.nd.O h.choose)) ?_ _ ?_ _ hc
      · have := (isAdic_iff.1 (X.nd.O_adic h.choose)).1 1
        simpa using this
      · intro y hy
        rw [RingHom.mem_ker]
        simp [(IsLocalRing.residue_eq_zero_iff y).2 hy]
    · simp [MonoidHom.ker_one]
  · intro i k v hk
    obtain ⟨u, hu, he⟩ := hchi i k v hk
    rcases hu with rfl | rfl
    · exact Or.inl he
    · exact Or.inr he
  · intro i σ Sig hP hcsd hinf
    have hg : BcGood D Rw σ Sig := ⟨fun p hp => ⟨(hP.1 p hp).1, (hP.1 p hp).2, hcsd p hp, hinf p hp⟩, hP.2.1,
      fun w hw => (hP.2.2 w hw).trans (hloc i σ w)⟩
    have hex : ∃ Sig, BcGood D Rw σ Sig := ⟨Sig, hg⟩
    show bcOf D Rw σ = _
    unfold bcOf
    rw [dif_pos hex]
    have h0 := hex.choose_spec
    refine hBU _ _ (fun p hp => ?_) h0.2.1 hg.2.1 (fun w hw => (h0.2.2 w hw).trans (hg.2.2 w hw).symm)
    rcases List.mem_append.1 hp with hp | hp
    · exact h0.1 p hp
    · exact hg.1 p hp
  · intro i σ Sig ρ hP hR
    refine ⟨?_, rbar_tie_at D Rw Pl X Y hCheb hloc hplB i σ Sig ρ hP hR⟩
    exact isSSRep_rbarOf Y σ (X.nd.w i)
  · intro i σ'
    show mtParOf Y (X.nd.mu i) (X.nd.j i) σ' = mtSup Y i σ'
    have hex : ∃ i', X.nd.mu i' = X.nd.mu i ∧ X.nd.j i' = X.nd.j i := ⟨i, rfl, rfl⟩
    unfold mtParOf
    rw [dif_pos hex]
    exact castMt_eq _ _ _ _ (hMt _ _ σ' hex.choose_spec.1 hex.choose_spec.2)
  · exact fun σ lam => isSSRep_rbarOf Y σ lam

end GlobalTheory.HeightCounting

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDataOkOfTrueColumnChoices
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.LevelLaw

theorem ok_reRep {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {S : GStep E K n}
    {ST : Finset (HeightOneSpectrum (𝓞 E))} {A : TDat S ST} {T : ℕ} (pref : ∀ b, S.D b → Prop) (h : A.Ok T) :
    TDat.Ok (S := S.reRep pref) { A with } T :=
  { h with }

theorem tied_reRep {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S : GStep E K n}
    {ST : Finset (HeightOneSpectrum (𝓞 E))} {A : TDat S ST} {T : ℕ} (pref : ∀ b, S.D b → Prop) (h : A.Tied T) :
    TDat.Tied (S := S.reRep pref) { A with } T :=
  { h with }

theorem atIn_ok : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ u a, (I.atIn u a).Ok := by
  intro B X I h u a
  obtain ⟨hX, hPr, -, -, hbig⟩ := base_fields_primes_ok B X
  have hQ : ∀ w ∈ I.Q a, ((B.primes X).T u : 𝓞 B.fields.E) ∉ w.asIdeal :=
    T_notMem_QE I.sel (I.tup a) u hPr h.sel_ok (h.T_mem u)
  exact
    { T_prime := hPr.T_prime u
      card_ST := (hPr.vT_card u).trans B.fields_f
      card_res := fun P => (card_res P.1).trans (hPr.vT_norm u P.1 P.2)
      lev := fun j => ok_reRep (I.pref u a j) (tdatAt_ok I.sel (I.tup a) (I.cst a) (I.idx a) (I.Tp a) hX hPr u j)
      tied := fun j => tied_reRep (I.pref u a j) (tdatAt_tied I.sel (I.tup a) (I.cst a) (I.idx a) (I.Tp a) hX hPr u hQ j)
      psi_ne := fun P => psiWeil_ne_one (xiUnitAt_vT B X u P).2
      free0 := stepAt_zero_free I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (I.Tp a) u hX hPr hbig (h.idx_ok a).zero_G
      duStar_pos := B.duStar_pos u
      Dstar_pos := B.Dstar_pos
      one_lt_gammaP := B.one_lt_gammaP }

end GlobalTheory.Mem.Col2.LevelLaw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemBesselExchangeGroupIffRootExchangeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_besselExchangeGroup_iff_rootExchange : ∀ (D : D7) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesselDatum A B ι) (ε : AE D), IsSplitIdem D ε → ∀ (i : Fin (d.ρ + 1)) (g : GA D B), g ∈ d.Ex ε i ↔ ∃ t, ε • t = t ∧ IsK B (vecA B (dual d i)) (iA ι t) g := by
  first | exact @GlobalTheory.RootExch.ExStruct.mem_Ex_iff | exact GlobalTheory.RootExch.ExStruct.mem_Ex_iff | (intros; apply GlobalTheory.RootExch.ExStruct.mem_Ex_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothVectorsModerateGrowthSmoothFrechetRepStatement
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_vectors_moderate_growth_smooth_frechet_rep : ∀ (n : ℕ) (ε : Fin n → Bool) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (ρ : Mx n → (E →L[ℂ] E)), ModRep ε ρ → IsClosed (Fam ε ρ : Set (List (lie (Jm ε)) → E)) ∧ ∃ (p : ℕ → Seminorm ℂ (Fam ε ρ)) (π dπ : Mx n → (Fam ε ρ →L[ℂ] Fam ε ρ)), IsSmoothModRep ε p π dπ ∧ (∀ (g : Mx n) (hg : g ∈ UJset ε) (v : Fam ε ρ) (l : List (lie (Jm ε))), (π g v).1 l = ρ g (v.1 (l.map (adInv hg)))) ∧ (∀ (X : lie (Jm ε)) (v : Fam ε ρ) (l : List (lie (Jm ε))), (dπ (X : Mx n) v).1 l = v.1 (l ++ [X])) ∧ ∀ v : Fam ε ρ, ‖v.1 []‖ ≤ p 0 v := by
  first | exact @GlobalTheory.TypeSum.SmoothFrechet.smooth_frechet_rep | exact GlobalTheory.TypeSum.SmoothFrechet.smooth_frechet_rep | (intros; apply GlobalTheory.TypeSum.SmoothFrechet.smooth_frechet_rep <;> assumption)
end


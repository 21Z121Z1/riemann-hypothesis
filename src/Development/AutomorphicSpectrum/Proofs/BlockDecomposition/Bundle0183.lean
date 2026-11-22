import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.Bridge
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0173
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0182
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0048
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0180
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0038
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0007
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0039
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0181
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeanValueFormula

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CartanLocalToGlobal
section
open Matrix Topology Filter

namespace GlobalTheory.CompanionTheory.LinRedFactor

open GlobalTheory.LinRed

variable {n : ℕ}

theorem isCompact_unitary_fin :
    IsCompact (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) := by
  have hc : IsCompact (Set.pi Set.univ fun _ : Fin n =>
      Set.pi Set.univ fun _ : Fin n => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine IsCompact.of_isClosed_subset (t := _) hc ?_ ?_
  · have : (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) =
        {A | A * Aᴴ = 1} := by
      ext A; exact Matrix.mem_unitaryGroup_iff
    rw [this]
    exact isClosed_eq (continuous_id.matrix_mul continuous_id.matrix_conjTranspose)
      continuous_const
  · intro A hA i _ j _
    simpa using entry_norm_bound_of_unitary hA i j

theorem unitary_mul_star {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) : U * Uᴴ = 1 :=
  Matrix.mem_unitaryGroup_iff.1 hU

theorem star_mul_unitary {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) : Uᴴ * U = 1 :=
  Matrix.mem_unitaryGroup_iff'.1 hU

theorem conj_mul_conj {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (s t : Matrix (Fin n) (Fin n) ℂ) :
    (Uᴴ * s * U) * (Uᴴ * t * U) = Uᴴ * (s * t) * U := by
  calc (Uᴴ * s * U) * (Uᴴ * t * U) = Uᴴ * s * (U * Uᴴ) * t * U := by
        simp only [Matrix.mul_assoc]
    _ = Uᴴ * (s * t) * U := by
        rw [unitary_mul_star hU]; simp only [Matrix.mul_one, Matrix.mul_assoc]

theorem tri_mul {U s t : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hs : (Uᴴ * s * U).BlockTriangular id) (ht : (Uᴴ * t * U).BlockTriangular id) :
    (Uᴴ * (s * t) * U).BlockTriangular id := by
  rw [← conj_mul_conj hU]
  exact hs.mul ht

theorem isClosed_tri (U : Matrix (Fin n) (Fin n) ℂ) :
    IsClosed {s : Matrix (Fin n) (Fin n) ℂ | (Uᴴ * s * U).BlockTriangular id} := by
  simp only [Matrix.BlockTriangular, Set.setOf_forall]
  refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => ?_
  exact isClosed_eq
    (((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_elem i j)
    continuous_const

theorem isCompact_maxCpt {G : Set (Matrix (Fin n) (Fin n) ℂ)} (hG : IsLinRed G) :
    IsCompact (maxCpt G) := by
  refine isCompact_unitary_fin.of_isClosed_subset ?_ Set.inter_subset_right
  refine isClosed_of_closure_subset fun x hx => ?_
  have hxU : x ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) :=
    closure_minimal Set.inter_subset_right isCompact_unitary_fin.isClosed hx
  exact ⟨hG.closed x (IsUnit.of_mul_eq_one _ (unitary_mul_star hxU))
    (closure_mono Set.inter_subset_left hx), hxU⟩

def Good (G : Set (Matrix (Fin n) (Fin n) ℂ)) (U g : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ k ∈ maxCpt G, ∃ s ∈ G, g = k * s ∧ (Uᴴ * s * U).BlockTriangular id

theorem good_nhds {G : Set (Matrix (Fin n) (Fin n) ℂ)} (hG : IsLinRed G)
    {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (h : ∀ᶠ g in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), g ∈ G → Good G U g)
    {g₀ : Matrix (Fin n) (Fin n) ℂ} (h₀ : Good G U g₀) :
    ∀ᶠ g in 𝓝 g₀, g ∈ G → Good G U g := by
  obtain ⟨k₀, hk₀, s₀, hs₀, rfl, ht₀⟩ := h₀
  have hkk : k₀ * k₀ᴴ = 1 := unitary_mul_star hk₀.2
  have hkk' : k₀ᴴ * k₀ = 1 := star_mul_unitary hk₀.2
  have hsu : IsUnit s₀ := hG.isUnit s₀ hs₀
  have hss : s₀ * s₀⁻¹ = 1 := Matrix.mul_nonsing_inv s₀ ((Matrix.isUnit_iff_isUnit_det s₀).1 hsu)
  have hss' : s₀⁻¹ * s₀ = 1 := Matrix.nonsing_inv_mul s₀ ((Matrix.isUnit_iff_isUnit_det s₀).1 hsu)
  have hφ : Continuous fun g : Matrix (Fin n) (Fin n) ℂ => k₀ᴴ * g * s₀⁻¹ :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have e : k₀ᴴ * (k₀ * s₀) * s₀⁻¹ = 1 := by
    rw [← Matrix.mul_assoc, hkk', Matrix.one_mul, hss]
  have ht : Tendsto (fun g : Matrix (Fin n) (Fin n) ℂ => k₀ᴴ * g * s₀⁻¹) (𝓝 (k₀ * s₀)) (𝓝 1) := by
    have := hφ.tendsto (k₀ * s₀)
    rwa [e] at this
  filter_upwards [ht.eventually h] with g hg hgG
  obtain ⟨k₁, hk₁, s₁, hs₁, e₁, t₁⟩ :=
    hg (hG.mul_mem _ (hG.mul_mem _ (hG.star_mem _ hk₀.1) _ hgG) _ (hG.inv_mem _ hs₀))
  refine ⟨k₀ * k₁, ⟨hG.mul_mem _ hk₀.1 _ hk₁.1, mul_mem hk₀.2 hk₁.2⟩, s₁ * s₀,
    hG.mul_mem _ hs₁ _ hs₀, ?_, tri_mul hU t₁ ht₀⟩
  calc g = k₀ * (k₀ᴴ * g * s₀⁻¹) * s₀ := by
        calc g = (k₀ * k₀ᴴ) * g * (s₀⁻¹ * s₀) := by
              rw [hkk, hss', Matrix.one_mul, Matrix.mul_one]
          _ = k₀ * (k₀ᴴ * g * s₀⁻¹) * s₀ := by simp only [Matrix.mul_assoc]
    _ = k₀ * k₁ * (s₁ * s₀) := by
        rw [e₁]; simp only [Matrix.mul_assoc]

theorem isClosed_factor {G : Set (Matrix (Fin n) (Fin n) ℂ)} (hG : IsLinRed G)
    (U : Matrix (Fin n) (Fin n) ℂ) :
    IsClosed {g : Matrix (Fin n) (Fin n) ℂ |
      ∃ k ∈ maxCpt G, (Uᴴ * (kᴴ * g) * U).BlockTriangular id} := by
  haveI : CompactSpace (maxCpt G) := isCompact_iff_compactSpace.1 (isCompact_maxCpt hG)
  have hC : IsClosed {p : maxCpt G × Matrix (Fin n) (Fin n) ℂ |
      (Uᴴ * ((p.1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * p.2) * U).BlockTriangular id} :=
    (isClosed_tri U).preimage
      ((continuous_subtype_val.comp continuous_fst).matrix_conjTranspose.matrix_mul continuous_snd)
  have := isClosedMap_snd_of_compactSpace _ hC
  convert this using 1
  ext g
  constructor
  · rintro ⟨k, hk, t⟩
    exact ⟨(⟨k, hk⟩, g), t, rfl⟩
  · rintro ⟨⟨k, g'⟩, t, rfl⟩
    exact ⟨k.1, k.2, t⟩

theorem good_iff {G : Set (Matrix (Fin n) (Fin n) ℂ)} (hG : IsLinRed G)
    {U g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ G) :
    Good G U g ↔ ∃ k ∈ maxCpt G, (Uᴴ * (kᴴ * g) * U).BlockTriangular id := by
  constructor
  · rintro ⟨k, hk, s, _, rfl, t⟩
    refine ⟨k, hk, ?_⟩
    rwa [← Matrix.mul_assoc kᴴ, star_mul_unitary hk.2, Matrix.one_mul]
  · rintro ⟨k, hk, t⟩
    refine ⟨k, hk, kᴴ * g, hG.mul_mem _ (hG.star_mem _ hk.1) _ hg, ?_, t⟩
    rw [← Matrix.mul_assoc, unitary_mul_star hk.2, Matrix.one_mul]

theorem factor_of_local : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}, GlobalTheory.LinRed.IsLinRed G →
    ∀ U ∈ Matrix.unitaryGroup (Fin n) ℂ,
    (∀ᶠ g in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), g ∈ G →
      ∃ k ∈ GlobalTheory.LinRed.maxCpt G, ∃ s ∈ G, g = k * s ∧ (Uᴴ * s * U).BlockTriangular id) →
    ∀ g ∈ G, ∃ k ∈ GlobalTheory.LinRed.maxCpt G, ∃ s ∈ G, g = k * s ∧ (Uᴴ * s * U).BlockTriangular id := by
  intro n G hG U hU h g hg
  haveI : PreconnectedSpace G := isPreconnected_iff_preconnectedSpace.1 hG.connected
  have hclosed : IsClosed {x : G | Good G U x.1} := by
    have e : {x : G | Good G U x.1} = Subtype.val ⁻¹' {g : Matrix (Fin n) (Fin n) ℂ |
        ∃ k ∈ maxCpt G, (Uᴴ * (kᴴ * g) * U).BlockTriangular id} := by
      ext x
      exact good_iff hG x.2
    rw [e]
    exact (isClosed_factor hG U).preimage continuous_subtype_val
  have hopen : IsOpen {x : G | Good G U x.1} := by
    rw [isOpen_iff_eventually]
    intro x hx
    have := (continuous_subtype_val.tendsto x).eventually (good_nhds hG hU h hx)
    filter_upwards [this] with y hy using hy y.2
  have hone : Good G U 1 := by
    refine ⟨1, ⟨hG.one_mem, one_mem _⟩, 1, hG.one_mem, by simp, ?_⟩
    rw [Matrix.mul_one, star_mul_unitary hU]
    exact Matrix.blockTriangular_one
  have huniv := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨⟨1, hG.one_mem⟩, hone⟩
  have hmem : (⟨g, hg⟩ : G) ∈ {x : G | Good G U x.1} := huniv ▸ Set.mem_univ _
  exact hmem

end GlobalTheory.CompanionTheory.LinRedFactor
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechFormsAddSmul
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech

namespace GlobalTheory.CompanionTheory.OmCech

theorem cechOmAdd_smul {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {ι : Type}
    (U : ι → X.Opens) (hU : iSup U = ⊤) (hUaff : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (⨅ a, U (i a)))
    (a j : ℕ) (r : K) (x : CO q U a j) :
    cechOmAdd q U hU hUaff a j (r • x) = r • cechOmAdd q U hU hUaff a j x := by
  letI := GlobalTheory.HodgeCoh.algΓ q
  apply (GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega q a) j).injective
  have h1 : ∀ z : CO q U a j, GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega q a) j (cechOmAdd q U hU hUaff a j z) =
      cechHAddEquivH.{0} U hU hUaff (GlobalTheory.HodgeCoh.Omega q a) j z :=
    fun z => (GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega q a) j).apply_symm_apply _
  have h2 := cechHAddEquivH_naturality.{0} U hU hUaff
    (smulHom (GlobalTheory.HodgeCoh.Omega q a) (algebraMap K Γ(X, ⊤) r)) j x
  have h3 := GlobalTheory.coh.toH_map K (smulHom (GlobalTheory.HodgeCoh.Omega q a) (algebraMap K Γ(X, ⊤) r)) j
    (cechOmAdd q U hU hUaff a j x)
  rw [h1] at h3 ⊢
  exact h2.trans h3.symm

end GlobalTheory.CompanionTheory.OmCech
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechH0PullCompat
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech

namespace GlobalTheory.CompanionTheory.CechZero

theorem cechHZeroEquiv_cls {X : TopCat.{0}} {ι : Type} (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0})
    (U : ι → Opens X) (hP : Presheaf.IsSheaf (Opens.grothendieckTopology X) P) (hU : iSup U = ⊤)
    (s : P.obj (op ⊤)) (σ : Cochain P U 0) (h : GroundTheory.Arith.SchemeCoh.d P U 0 σ = 0)
    (hσ : σ = (globalCocycle P U s).1) :
    GroundTheory.Arith.SchemeCoh.cechHZeroEquiv P U hP hU (GroundTheory.Arith.SchemeCoh.cls σ h) = s := by
  subst hσ
  simp only [GroundTheory.Arith.SchemeCoh.cechHZeroEquiv, AddEquiv.trans_apply]
  exact (globalCocycleEquiv P U hP hU).symm_apply_apply s

theorem pullCoch_globalCocycle {X Y : TopCat.{0}} (f : X ⟶ Y) {P : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{0}}
    {Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}} (φ : P ⟶ (Opens.map f).op ⋙ Q)
    {κ ι : Type} (V : κ → Opens Y) (U : ι → Opens X) (τ : ι → κ)
    (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i))) (s : P.obj (op ⊤)) :
    pullCoch f φ V U τ hτ 0 (globalCocycle P V s).1 =
      (globalCocycle Q U (GroundTheory.Arith.SchemeCoh.res Q (le_top : (⊤ : Opens X) ≤ (Opens.map f).obj ⊤)
        (φ.app (op ⊤) s))).1 := by
  funext t
  change GroundTheory.Arith.SchemeCoh.res Q _ (φ.app _ (GroundTheory.Arith.SchemeCoh.res P _ s)) =
    GroundTheory.Arith.SchemeCoh.res Q _ (GroundTheory.Arith.SchemeCoh.res Q _ (φ.app (op ⊤) s))
  rw [app_res_map, res_res, res_res]

theorem zeroEquiv_eq_equivZero {X : TopCat.{0}} (F : AbSheaf X) (W : Opens X) (x : Sheaf.H'.{0} F 0 W) :
    GlobalTheory.SiteCoh.zeroEquiv F W x = GlobalTheory.SheafLES.equivZero.{0} F W x := by
  obtain ⟨φ, rfl⟩ := (Abelian.Ext.mk₀_bijective _ _).surjective x
  rw [GlobalTheory.SheafLES.equivZero_mk₀]
  exact GlobalTheory.SiteCoh.zeroEquiv_mk₀ F W φ

theorem hPull_zero {X Y : TopCat.{0}} (f : X ⟶ Y) {G : AbSheaf Y} {G' : AbSheaf X}
    (φ : G ⟶ (push f).obj G') (z : Sheaf.H.{0} G 0) :
    Sheaf.H.equiv₀ G' isTerminalTop (hPull f φ 0 z) =
      GroundTheory.Arith.SchemeCoh.res G'.obj (le_top : (⊤ : Opens X) ≤ (Opens.map f).obj ⊤)
        (φ.hom.app (op ⊤) (Sheaf.H.equiv₀ G isTerminalTop z)) := by
  obtain ⟨y, rfl⟩ := (GlobalTheory.SiteCoh.terminalEquiv G 0 isTerminalTop).surjective z
  change Sheaf.H.equiv₀ G' isTerminalTop (GlobalTheory.SiteCoh.terminalEquiv G' 0 isTerminalTop
    (pull.{0, 0} f φ 0 (homOfLE le_top : (⊤ : Opens X) ⟶ (Opens.map f).obj ⊤)
      ((GlobalTheory.SiteCoh.terminalEquiv G 0 isTerminalTop).symm
        (GlobalTheory.SiteCoh.terminalEquiv G 0 isTerminalTop y)))) = _
  rw [AddEquiv.symm_apply_apply, GlobalTheory.SiteCoh.equiv₀_terminalEquiv,
    GlobalTheory.SiteCoh.equiv₀_terminalEquiv, zeroEquiv_eq_equivZero, zeroEquiv_eq_equivZero,
    GlobalTheory.SheafPull.equivZero_pull]
  rfl

theorem cechHZeroEquivH_pull {X Y : TopCat.{0}} (f : X ⟶ Y) {κ ι : Type} (V : κ → Opens Y)
    (hV : iSup V = ⊤) (U : ι → Opens X) (hU : iSup U = ⊤) (τ : ι → κ)
    (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i)))
    {G : AbSheaf Y} {G' : AbSheaf X} (φ : G ⟶ (push f).obj G') (x : GroundTheory.Arith.SchemeCoh.cechH G.obj V 0) :
    (GroundTheory.Arith.SchemeCoh.cechHZeroEquivH G' U hU : GroundTheory.Arith.SchemeCoh.cechH G'.obj U 0 ≃+ Sheaf.H.{0} G' 0) (cechPullH f φ.hom V U τ hτ 0 x) =
      hPull f φ 0 ((GroundTheory.Arith.SchemeCoh.cechHZeroEquivH G V hV : GroundTheory.Arith.SchemeCoh.cechH G.obj V 0 ≃+ Sheaf.H.{0} G 0) x) := by
  obtain ⟨σ, hσ, rfl⟩ := exists_cls x
  obtain ⟨s, hs⟩ := globalCocycle_surjective G.obj V G.property hV ⟨σ, (mem_cocycles σ).2 hσ⟩
  have hσs : σ = (globalCocycle G.obj V s).1 := (congrArg Subtype.val hs).symm
  apply (Sheaf.H.equiv₀ G' isTerminalTop).injective
  rw [hPull_zero, cechPullH_cls]
  simp only [GroundTheory.Arith.SchemeCoh.cechHZeroEquivH, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
  rw [cechHZeroEquiv_cls G.obj V G.property hV s σ hσ hσs]
  refine cechHZeroEquiv_cls G'.obj U G'.property hU _ _ _ ?_
  rw [hσs]
  exact pullCoch_globalCocycle f φ.hom V U τ hτ s

end GlobalTheory.CompanionTheory.CechZero
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechShortExactPullCompat
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech

namespace GlobalTheory.CompanionTheory.OmCechDelta

theorem app_res_nat {X : TopCat.{0}} {Q Q₂ : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}} (a : Q ⟶ Q₂)
    {A B : Opens X} (h : A ≤ B) (x : Q.obj (op B)) :
    a.app (op A) (res Q h x) = res Q₂ h (a.app (op B) x) := by
  exact NatTrans.naturality_apply a (homOfLE h).op x

theorem push_pullCoch {X Y : TopCat.{0}} (f : X ⟶ Y) {κ ι : Type} (V : κ → Opens Y) (U : ι → Opens X)
    (τ : ι → κ) (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i)))
    {P P₂ : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{0}} {Q Q₂ : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}}
    (a : P ⟶ P₂) (a' : Q ⟶ Q₂) (φ : P ⟶ (Opens.map f).op ⋙ Q) (φ₂ : P₂ ⟶ (Opens.map f).op ⋙ Q₂)
    (h : ∀ W x, φ₂.app W (a.app W x) = a'.app _ (φ.app W x)) (n : ℕ) (σ : Cochain P V n) :
    push U a' n (pullCoch f φ V U τ hτ n σ) = pullCoch f φ₂ V U τ hτ n (push V a n σ) := by
  funext t
  exact (app_res_nat a' _ _).trans (congrArg (res Q₂ _) (h _ _).symm)

theorem cechPullH_delta : ∀ {X Y : TopCat.{0}} (f : X ⟶ Y) {κ ι : Type} (V : κ → Opens Y) (U : ι → Opens X) (τ : ι → κ)
    (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i))) {F I Q : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{0}}
    {F' I' Q' : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}} {g₁ : F ⟶ I} {g₂ : I ⟶ Q} {g₁' : F' ⟶ I'} {g₂' : I' ⟶ Q'}
    (hC : IsCechShortExact V g₁ g₂) (hC' : IsCechShortExact U g₁' g₂') (φ₁ : F ⟶ (Opens.map f).op ⋙ F')
    (φ₂ : I ⟶ (Opens.map f).op ⋙ I') (φ₃ : Q ⟶ (Opens.map f).op ⋙ Q')
    (h₁₂ : ∀ W x, φ₂.app W (g₁.app W x) = g₁'.app _ (φ₁.app W x))
    (h₂₃ : ∀ W x, φ₃.app W (g₂.app W x) = g₂'.app _ (φ₂.app W x)) (n : ℕ) (σ : cocycles Q V n),
    cechPullH f φ₁ V U τ hτ (n + 1) (hC.delta n σ) =
      hC'.delta n ⟨pullCoch f φ₃ V U τ hτ n σ.1, pullCoch_mem_cocycles f φ₃ V U τ hτ σ.2⟩ := by
  intro X Y f κ ι V U τ hτ F I Q F' I' Q' g₁ g₂ g₁' g₂' hC hC' φ₁ φ₂ φ₃ h₁₂ h₂₃ n σ
  obtain ⟨t, ρ, hρ, ht, hρt, hc⟩ := hC.delta_spec n σ
  have h1 : push U g₂' n (pullCoch f φ₂ V U τ hτ n t) = pullCoch f φ₃ V U τ hτ n σ.1 := by
    rw [push_pullCoch f V U τ hτ g₂ g₂' φ₂ φ₃ h₂₃ n t, ht]
  have h2 : push U g₁' (n + 1) (pullCoch f φ₁ V U τ hτ (n + 1) ρ) =
      d I' U n (pullCoch f φ₂ V U τ hτ n t) := by
    rw [push_pullCoch f V U τ hτ g₁ g₁' φ₁ φ₂ h₁₂ (n + 1) ρ, hρt, pullCoch_d]
  have h3 : d F' U (n + 1) (pullCoch f φ₁ V U τ hτ (n + 1) ρ) = 0 := by
    rw [← pullCoch_d, hρ, map_zero]
  rw [hc, cechPullH_cls]
  exact hC'.deltaRel_unique ⟨pullCoch f φ₂ V U τ hτ n t, pullCoch f φ₁ V U τ hτ (n + 1) ρ, h3, h1, h2, rfl⟩
    (hC'.delta_spec n ⟨pullCoch f φ₃ V U τ hτ n σ.1, pullCoch_mem_cocycles f φ₃ V U τ hτ σ.2⟩)

end GlobalTheory.CompanionTheory.OmCechDelta
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompatibleRootsLiftToTilt
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.Untilt

section Adic

variable {R : Type*} [CommRing R]

theorem smodEq_span_pow_iff (π x y : R) (n : ℕ) :
    x ≡ y [SMOD (Ideal.span {π} ^ n • (⊤ : Submodule R R))] ↔ π ^ n ∣ x - y := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem eq_zero_of_forall_pow_dvd {π x : R} (h : IsHausdorff (Ideal.span {π}) R)
    (hx : ∀ n : ℕ, π ^ n ∣ x) : x = 0 :=
  h.haus x fun n => (smodEq_span_pow_iff π x 0 n).2 (by simpa using hx n)

theorem exists_limit_of_pow_dvd {π : R} (h : IsPrecomplete (Ideal.span {π}) R) (f : ℕ → R)
    (hf : ∀ n : ℕ, π ^ n ∣ f (n + 1) - f n) : ∃ L, ∀ n : ℕ, π ^ n ∣ f n - L :=
  _root_.UpperTheory.Reformulated.B.Yra6.main h f hf

theorem pow_pow_of_compatible {M : Type*} [Monoid M] {l : ℕ} {v : ℕ → M}
    (hv : ∀ i, v (i + 1) ^ l = v i) (i j : ℕ) : v (i + j) ^ l ^ j = v i := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', pow_mul, ← add_assoc, hv, ih]

end Adic

variable {l : ℕ} [Fact l.Prime] (A : PAlg l)

theorem sub_pow_pow (x y : A.A) (j : ℕ) : (x - y) ^ l ^ j = x ^ l ^ j - y ^ l ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, pow_mul, ih, pow_mul, pow_mul]
    exact map_sub A.frob _ _

theorem exists_limit_pow (b : ℕ → A.A) (hb : ∀ j, A.pi ∣ b (j + 1) ^ l - b j) (i : ℕ) :
    ∃ L, ∀ n : ℕ, A.pi ^ n ∣ b (i + n) ^ l ^ n - L := by
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  refine exists_limit_of_pow_dvd (π := A.pi) A.compl.toIsPrecomplete
    (fun n => b (i + n) ^ l ^ n) fun n => ?_
  have e : b (i + (n + 1)) ^ l ^ (n + 1) - b (i + n) ^ l ^ n
      = (b (i + n + 1) ^ l - b (i + n)) ^ l ^ n := by
    rw [sub_pow_pow, ← pow_mul, ← pow_succ', add_assoc]
  change A.pi ^ n ∣ b (i + (n + 1)) ^ l ^ (n + 1) - b (i + n) ^ l ^ n
  rw [e]
  exact (pow_dvd_pow _ (Nat.lt_pow_self hl).le).trans (pow_dvd_pow_of_dvd (hb _) _)

theorem exists_compatible_roots_of_sharp : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (u : ℕ → A.U),
    (∀ i, u (i + 1) ^ l = u i) →
    ∃ a : ℕ → A.A, (∀ i, a (i + 1) ^ l = a i) ∧ ∀ i, A.sharp (a i) = u i := by
  intro l _ A u hu
  obtain ⟨hsurj, hker⟩ := sharp_map_surjective_ker A
  choose b hb using fun j => hsurj (Ideal.Quotient.mk _ (u j))
  have hbd : ∀ j, A.pi ∣ b (j + 1) ^ l - b j := fun j => by
    rw [← Ideal.mem_span_singleton]
    rw [← hker, RingHom.mem_ker, map_sub, map_pow, hb, hb, ← map_pow, hu, sub_self]
  choose a ha using exists_limit_pow A b hbd
  have hA : IsHausdorff (Ideal.span {A.pi}) A.A := A.compl.toIsHausdorff
  have hroot : ∀ i, a (i + 1) ^ l = a i := fun i => by
    refine sub_eq_zero.1 (eq_zero_of_forall_pow_dvd hA fun n => ?_)
    have h1 : A.pi ^ n ∣ b (i + 1 + n) ^ l ^ (n + 1) - a (i + 1) ^ l := by
      rw [pow_succ, pow_mul]
      exact (ha (i + 1) n).trans (sub_dvd_pow_sub_pow _ _ l)
    have h2 : A.pi ^ n ∣ b (i + 1 + n) ^ l ^ (n + 1) - a i := by
      have := ha i (n + 1)
      rw [show i + (n + 1) = i + 1 + n by ring] at this
      exact (pow_dvd_pow _ (Nat.le_succ n)).trans this
    have := dvd_sub h2 h1
    simpa using this
  have hmod : ∀ i, A.pi ∣ a i - b i := fun i => by
    have h1 := ha i 1
    rw [pow_one, pow_one] at h1
    have := dvd_sub (hbd i) h1
    simpa using this
  have hl1 : ∀ i, (l : A.U) ∣ A.sharp (a i) - u i := fun i => by
    have h0 : A.aToU1 (a i) = A.aToU1 (b i) := by
      rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, hker, Ideal.mem_span_singleton]
      exact hmod i
    rw [hb, sharpMap_eq] at h0
    have := Ideal.Quotient.eq.1 h0
    rwa [pow_one, Ideal.mem_span_singleton] at this
  refine ⟨a, hroot, fun i => sub_eq_zero.1 ?_⟩
  refine eq_zero_of_forall_pow_dvd (π := (l : A.U)) (GlobalTheory.T.untilt_adic_complete A).toIsHausdorff fun n => ?_
  have h1 := dvd_sub_pow_of_dvd_sub (hl1 (i + n)) n
  rw [← map_pow, pow_pow_of_compatible hroot, pow_pow_of_compatible hu] at h1
  exact (pow_dvd_pow _ (Nat.le_succ n)).trans h1

end GlobalTheory.CompanionTheory.Untilt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexHessianLogFubiniStudyStatement
section
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_hessian_log_fubini_study : ∀ (d : ℕ) (β : Type) [Fintype β] (U : Set (V d)) (f : β → V d → ℂ), IsOpen U → (∀ j, DifferentiableOn ℂ (f j) U) → ∀ z ∈ U, cHess d (fun v => ((Real.log (1 + ∑ j, ‖f j v‖ ^ 2) : ℝ) : ℂ)) z = fsLevi (fun j => f j z) (Matrix.of fun j a => fderiv ℂ (f j) z (EuclideanSpace.single a 1)) := by
  first | exact @GlobalTheory.CompanionTheory.FSCrofton.cHess_log_one_add_sum | exact GlobalTheory.CompanionTheory.FSCrofton.cHess_log_one_add_sum | (intros; apply GlobalTheory.CompanionTheory.FSCrofton.cHess_log_one_add_sum <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineGradedPiecesDescriptionStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_graded_pieces_description : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (r : ℕ), (∀ z ∈ A.Fil0 r, ∃ w : A.W, z - algebraMap A.W A.Acr0 w * A.dxi0 r ∈ A.Fil0 (r + 1)) ∧ (∀ w : A.W, algebraMap A.W A.Acr0 w * A.dxi0 r ∈ A.Fil0 (r + 1) ↔ w ∈ Ideal.span {A.xi}) ∧ ∀ z ∈ A.Fil0 r, ∃ (N : ℕ) (w : A.W), (l : A.Acr0) ^ N * z = algebraMap A.W A.Acr0 (A.xi ^ r * w) := by
  first | exact @GlobalTheory.CompanionTheory.PerfFil.crystalline_filtration_graded_pieces | exact GlobalTheory.CompanionTheory.PerfFil.crystalline_filtration_graded_pieces | (intros; apply GlobalTheory.CompanionTheory.PerfFil.crystalline_filtration_graded_pieces <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueIdempotentLiftTilt
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.Untilt

theorem existsUnique_idempotent_sharp {l : ℕ} [Fact l.Prime] (A : PAlg l) (e : A.U)
    (he : IsIdempotentElem e) : ∃! e₀ : A.A, IsIdempotentElem e₀ ∧ A.sharp e₀ = e := by
  obtain ⟨hsurj, hker⟩ := sharp_map_surjective_ker A
  haveI hcA : IsAdicComplete (Ideal.span {A.pi ^ 1}) A.A := by
    rw [pow_one]; exact A.compl
  haveI hcA' : IsAdicComplete (Ideal.span {A.pi}) A.A := A.compl
  haveI hcU : IsAdicComplete (Ideal.span {(l : A.U)}) A.U := GlobalTheory.T.untilt_adic_complete A
  have hmemker : ∀ x y : A.A, A.aToU1 x = A.aToU1 y →
      Ideal.Quotient.mk (Ideal.span {A.pi ^ 1}) x = Ideal.Quotient.mk _ y := by
    intro x y h
    apply Ideal.Quotient.eq.2
    rw [pow_one, ← hker, RingHom.mem_ker, map_sub, h, sub_self]
  have hsharp_idem : ∀ x : A.A, IsIdempotentElem x → IsIdempotentElem (A.sharp x) := fun x hx =>
    hx.map A.sharp
  have hU := GlobalTheory.CompanionTheory.IdemLift.existsUnique_idempotent_lift (l : A.U) 1 one_ne_zero
    (Ideal.Quotient.mk _ e) (he.map (Ideal.Quotient.mk _))
  obtain ⟨a, ha⟩ := hsurj (Ideal.Quotient.mk _ e)
  have haid : IsIdempotentElem (Ideal.Quotient.mk (Ideal.span {A.pi ^ 1}) a) := by
    have : A.aToU1 (a * a) = A.aToU1 a := by
      rw [map_mul, ha]
      exact congrArg _ he |>.trans rfl
    have h2 := hmemker _ _ this
    rw [map_mul] at h2
    exact h2
  obtain ⟨e₀, ⟨he₀, hmk⟩, huniq⟩ := GlobalTheory.CompanionTheory.IdemLift.existsUnique_idempotent_lift A.pi 1 one_ne_zero
    (Ideal.Quotient.mk _ a) haid
  have hcong : ∀ x y : A.A, Ideal.Quotient.mk (Ideal.span {A.pi ^ 1}) x = Ideal.Quotient.mk _ y →
      A.aToU1 x = A.aToU1 y := by
    intro x y h
    have h3 := Ideal.Quotient.eq.1 h
    rw [pow_one, ← hker, RingHom.mem_ker, map_sub] at h3
    exact sub_eq_zero.1 h3
  refine ⟨e₀, ⟨he₀, ?_⟩, ?_⟩
  · refine hU.unique ⟨hsharp_idem _ he₀, ?_⟩ ⟨he, rfl⟩
    rw [← A.sharpMap_eq, hcong _ _ hmk, ha]
  · rintro e₁ ⟨he₁, hs₁⟩
    refine huniq e₁ ⟨he₁, ?_⟩
    rw [← hmk]
    apply hmemker
    have hs₀ : A.sharp e₀ = e := hU.unique ⟨hsharp_idem _ he₀, by
      rw [← A.sharpMap_eq, hcong _ _ hmk, ha]⟩ ⟨he, rfl⟩
    rw [A.sharpMap_eq, A.sharpMap_eq, hs₁, hs₀]

end GlobalTheory.CompanionTheory.Untilt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalBinaryGramIntegralStatement
section
open PositivityTheory.Rg.Mass
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_binary_gram_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (J : Matrix (Fin 2) (Fin 2) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
  (lam : Measure (Fv F v)), IsStdV v lam → ∀ (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin 2 → Fv F v ⊗[F] E)),
  IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 2) (coordHerm (Fv F v) σ b lam 1) m →
  ∀ A : Set (Fin 1 → Fin 2 → Fv F v ⊗[F] E), IsCompact A → IsOpen A → A ⊆ {X | IsUnit (gramR (Fv F v) σ J X).det} →
  Continuous (fun s : Fv F v => (m (hermScal (Fv F v) σ s) A).toReal) ∧
  HasCompactSupport (fun s : Fv F v => (m (hermScal (Fv F v) σ s) A).toReal) ∧
  ENNReal.ofReal (∫ s, (m (hermScal (Fv F v) σ s) A).toReal ∂lam) = coordW (Fv F v) b lam 1 2 A := by
  first | exact @GlobalTheory.CompanionTheory.SW.FibreCpt.fibre_masses | exact GlobalTheory.CompanionTheory.SW.FibreCpt.fibre_masses | (intros; apply GlobalTheory.CompanionTheory.SW.FibreCpt.fibre_masses <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeanValueFormulaStatement
section
open PositivityTheory.Rg.Mass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mean_value_formula : Equi → CountBd → MeanVal := by
  first | exact @GlobalTheory.CompanionTheory.Mass.MeanV.meanVal_of_equi_countBd | exact GlobalTheory.CompanionTheory.Mass.MeanV.meanVal_of_equi_countBd | (intros; apply GlobalTheory.CompanionTheory.Mass.MeanV.meanVal_of_equi_countBd <;> assumption)
end


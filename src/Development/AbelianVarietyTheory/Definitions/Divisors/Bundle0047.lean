import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GridTestLatticeLargestSlopeBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClPlusAndExistsCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalOfIsCuspidal
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsTestLatUnique
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV Formalism.UG Formalism.IndefR
open GlobalTheory.ChiGrid GlobalTheory.TestLat GlobalTheory.CoefModel
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder

namespace GlobalTheory.FunObj.TestLatModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc}

theorem finE_rat (γ : GQ (Xp G)) (γE : UR D.sp.cm (Xp G).gram) (h : Bridge.IsRatMat (Xp G) γ γE.1) :
    Formalism.IndefR.Lev.finE (Xp G) γ = ratIn G γE := by
  have h' : matHom (Xp G) γ = bc (incA D) γE.1 := h
  apply Units.ext
  show ((matHom (Xp G) γ).1.map _).map _ = γE.1.1.map _
  rw [h']
  ext i j
  rfl

theorem map_rhoVr {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (lam : D.what₂.Tau → DomWeight V.rank) (γ : GQ V)
    (γE : GL (Fin V.rank) D.host.E) (h : Bridge.IsRatMat V γ γE) (x : GA D V) (v : VV D.what₂.LL lam) :
    rhoK lam (invTrK (realGL θ V (γ.1 * x)⁻¹)) (mapVV D.what₂.embLL lam (rhoVr (labLL D) lam γE v)) =
      rhoK lam (invTrK (realGL θ V x⁻¹)) (mapVV D.what₂.embLL lam v) := by
  have hlab : ∀ τ x, D.what₂.embLL (labLL D τ x) = tauE D τ x := fun τ x =>
    DFunLike.congr_fun (GlobalTheory.ThetaFiresProbe.labE_fixed τ) x
  have e : (fun τ => Formalism.UG.bc D.what₂.embLL (invTrK (embGL (labLL D) γE) τ)) = invTrK (realGL θ V γ) := by
    funext τ
    apply Units.ext
    rw [bc_coe, invTrK_coe, invTrK_coe, realGL_rat hθ V γ γE h, embGL_inv, ← map_inv, embGL_coe, bc_coe]
    ext a b
    exact hlab _ _
  have e2 : (γ.1 * x)⁻¹ * γ.1 = x⁻¹ := by group
  show rhoK _ _ (mapVV _ _ (rhoK lam (invTrK (embGL (labLL D) γE)) _)) = _
  rw [mapVV_rhoK, e, ← Module.End.mul_apply, ← map_mul (rhoK lam), ← map_mul invTrK, ← map_mul (realGL θ V), e2]

theorem scal_left {θ : InfFam D} (hθ : IsInfFam θ) (ξ : Module.Dual ℂ (VV ℂ (LaP G))) (Ψ : GLf G → WtSp G)
    (hΨ : ∀ γ g, Ψ (ratIn G γ * g) = rhoW G γ (Ψ g)) (γ : GQ (Xp G)) (γE : UR D.sp.cm (Xp G).gram)
    (h : Bridge.IsRatMat (Xp G) γ γE.1) (x : GA D (Xp G)) : scal θ ξ Ψ (γ.1 * x) = scal θ ξ Ψ x := by
  have e : Ψ (Formalism.IndefR.Lev.finE (Xp G) (γ.1 * x)) = rhoVr (labLL D) (LaP G) γE.1 (Ψ (Formalism.IndefR.Lev.finE (Xp G) x)) := by
    rw [map_mul (Formalism.IndefR.Lev.finE (Xp G)), finE_rat γ γE h, hΨ]
    rfl
  unfold scal
  rw [e, map_rhoVr hθ (Xp G) (LaP G) γ γE.1 h]

theorem pair_rhoW (γ : UR D.sp.cm (Xp G).gram) (x y : WtSp G) :
    pairK (LaP G) (gramKd (emb D) (Xp G).gram) (rhoW G γ x) (rhoW G γ y) = pairK (LaP G) (gramKd (emb D) (Xp G).gram) x y := by
  refine pairInv D.what₂.LL _ _ (LaP G) _ (invTrK (embGL (emb D) γ.1)) (fun τ => ?_) x y
  have h0 : cT (D.sp.cm.sig : D.host.E →+* D.host.E) γ.1.1 * (Xp G).gram * γ.1.1 = (Xp G).gram := γ.2
  have hg : (γ.1.1.map (emb D τ))ᴴ * (Xp G).gram.map (emb D τ) * γ.1.1.map (emb D τ) = (Xp G).gram.map (emb D τ) := by
    have h1 := congrArg (fun M => M.map (emb D τ)) h0
    simp only [Matrix.map_mul] at h1
    have h2 : (γ.1.1.map (emb D τ))ᴴ = (cT (D.sp.cm.sig : D.host.E →+* D.host.E) γ.1.1).map (emb D τ) := by
      ext i j
      exact star_emb τ _
    rw [h2, h1]
  have h := congrArg (fun M => (M⁻¹)ᵀ) hg
  simp only [Matrix.mul_inv_rev, Matrix.transpose_mul] at h
  rw [invTrK_coe, gramKd, Matrix.coe_units_inv, embGL_coe]
  have h3 : ∀ A : Matrix (Fin (Xp G).rank) (Fin (Xp G).rank) D.what₂.LL, A⁻¹ᵀᴴ = Aᴴ⁻¹ᵀ := fun A => by
    rw [← Matrix.conjTranspose_nonsing_inv]; rfl
  rw [h3, h]

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
  (Λ : Submodule (𝓞 E) (Fin n → E))

theorem mem_globLat_rat (γ : GL (Fin n) E) (g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (x : Fin n → E) :
    γ.1 *ᵥ x ∈ CS.globLat (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * g) Λ ↔ x ∈ CS.globLat g Λ := by
  have e : (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((γ.1 *ᵥ x) i)) =
      (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ).1 *ᵥ fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i) := by
    funext i
    exact RingHom.map_mulVec _ _ _ i
  simp only [CS.globLat, ← SetLike.mem_coe, Submodule.coe_set_mk, AddSubmonoid.coe_set_mk, AddSubsemigroup.coe_set_mk, Set.mem_ofPred_eq]
  rw [e, mulVec_mulVec, ← Units.val_mul, _root_.mul_inv_rev, inv_mul_cancel_right]

theorem globLat_mul [StarRing E] (g k : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hk : k ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := F) Λ)) : CS.globLat (g * k) Λ = CS.globLat g Λ := by
  ext x
  simp only [CS.globLat, ← SetLike.mem_coe, Submodule.coe_set_mk, AddSubmonoid.coe_set_mk, AddSubsemigroup.coe_set_mk, Set.mem_ofPred_eq]
  rw [_root_.mul_inv_rev, Units.val_mul, ← mulVec_mulVec]
  exact ((inv_mem hk : k⁻¹ ∈ _) _).symm

end Gen

theorem mem_latOf_rat (γ : UR D.sp.cm (Xp G).gram) (g : GLf G) (x : Fin (Xp G).rank → D.host.E) :
    γ.1.1 *ᵥ x ∈ latOf G (ratIn G γ * g) ↔ x ∈ latOf G g := mem_globLat_rat _ γ.1 g x

theorem latOf_mul (g : GLf G) {k : GLf G} (hk : k ∈ G.Kplus) : latOf G (g * k) = latOf G g :=
  globLat_mul _ g k hk.2.1

theorem psi_ne_zero (rp : ClassReps G) (hN : rp.Neat) {n : ℕ} (e : Fin n ≃ TestIx G × VVIdx (LaP G)) (a : Fin n) :
    psi rp e a (rp.x (e a).1.2) ≠ 0 := by
  rw [psi, rp.gridClassReps_delta_apply_rep hN, if_pos rfl]
  exact (bVV D.what₂.LL (LaP G)).ne_zero _

theorem isTestLat_unique {rp : ClassReps G} {n : ℕ} {e : Fin n ≃ TestIx G × VVIdx (LaP G)} {X X' M M'}
    (h : IsTestLat G rp n e X M) (h' : IsTestLat G rp n e X' M') : M = M' := h.2.trans h'.2.symm

theorem exists_testLat (h : (L.ΛY 0).FG) (rp : ClassReps G) : ∃ n e X M, 0 < n ∧ IsTestLat G rp n e X M := by
  obtain ⟨n, ⟨e⟩⟩ := exists_coords G h
  obtain ⟨X, M, hM⟩ := exists_isTestLat G rp n e
  obtain ⟨i⟩ := SlopeModel.nonempty_idx (LaP G)
  exact ⟨n, e, X, M, (e.symm (⟨fun _ => default, Quotient.mk'' 1⟩, i)).pos, hM⟩

end GlobalTheory.FunObj.TestLatModel

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IwahoriRegularSeparable
section
open MeasureTheory Matrix GlobalTheory.PRep GlobalTheory.SmGL

noncomputable section

namespace GlobalTheory.Block5c

def FinTF : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  (ξ : Representation ℂ Γ W),
  Finite (DoubleCoset.Quotient (Γ : Set G) (K : Set G)) → (∀ x : G, Finite (GlobalTheory.LKLoc.locPart Γ K x)) →
  ∀ f : G → ℂ, (∀ k ∈ K, ∀ k' ∈ K, ∀ g, f (k * g * k') = f g) → (Function.support (fun q : G ⧸ K => f q.out)).Finite →
  ∀ M : Submodule ℂ (G → W), (∀ φ, φ ∈ M ↔ (∀ γ : Γ, ∀ g, φ ((γ : G) * g) = ξ γ (φ g)) ∧ ∀ k ∈ K, ∀ g, φ (g * k) = φ g) →
  ∀ T : M →ₗ[ℂ] M, (∀ φ : M, ∀ g, (T φ : G → W) g = ∑ᶠ h : G ⧸ K, f h.out • (φ : G → W) (g * h.out)) →
  LinearMap.trace ℂ M T = ∑ᶠ q : DoubleCoset.Quotient (Γ : Set G) (K : Set G),
    (1 / (Nat.card (GlobalTheory.LKLoc.locPart Γ K q.out) : ℂ)) * ∑ᶠ γ : Γ, f (q.out⁻¹ * γ * q.out) * LinearMap.trace ℂ W (ξ γ)

def FinTFOrb : Prop :=
  ∀ (G : Type) [Group G] (Γ K : Subgroup G) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  (ξ : Representation ℂ Γ W),
  Finite (DoubleCoset.Quotient (Γ : Set G) (K : Set G)) → (∀ x : G, Finite (GlobalTheory.LKLoc.locPart Γ K x)) →
  ∀ f : G → ℂ, (∀ k ∈ K, ∀ k' ∈ K, ∀ g, f (k * g * k') = f g) → (Function.support (fun q : G ⧸ K => f q.out)).Finite →
  ∀ R : Set Γ, (∀ γ : Γ, ∃! ρ, ρ ∈ R ∧ IsConj γ ρ) →
  ∑ᶠ q : DoubleCoset.Quotient (Γ : Set G) (K : Set G),
    (1 / (Nat.card (GlobalTheory.LKLoc.locPart Γ K q.out) : ℂ)) * ∑ᶠ γ : Γ, f (q.out⁻¹ * γ * q.out) * LinearMap.trace ℂ W (ξ γ)
  = ∑ᶠ ρ ∈ R, LinearMap.trace ℂ W (ξ ρ) *
      ∑ᶠ q : DoubleCoset.Quotient ((Subgroup.centralizer {(ρ : G)} ⊓ Γ : Subgroup G) : Set G) (K : Set G),
        (1 / (Nat.card (GlobalTheory.LKLoc.locPart (Subgroup.centralizer {(ρ : G)} ⊓ Γ) K q.out) : ℂ)) * f (q.out⁻¹ * ρ * q.out)

def CuspOrbZero : Prop :=
  ∀ (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (f : GL ι K → ℂ), IsLocallyConstant f → HasCompactSupport f →
  (∀ (a b : ℕ) (e : ι ≃ Fin a ⊕ Fin b), 0 < a → 0 < b → ∀ (μ : Measure (Fin a → Fin b → K)), μ.IsAddHaarMeasure →
    ∀ u : (Fin a → Fin b → K) → GL ι K,
      (∀ X, (u X : Matrix ι ι K) = Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) →
      ∀ g h : GL ι K, ∫ X, f (g * (h⁻¹ * u X * h)) ∂μ = 0) →
  ∀ γ : GL ι K, (γ : Matrix ι ι K).charpoly.Separable → ¬ Irreducible (γ : Matrix ι ι K).charpoly →
  ∀ (K0 K1 : Subgroup (GL ι K)), IsOpen (K0 : Set (GL ι K)) → IsCompact (K0 : Set (GL ι K)) →
    IsOpen (K1 : Set (GL ι K)) → IsCompact (K1 : Set (GL ι K)) →
    (∀ k ∈ K0, ∀ k' ∈ K0, ∀ g, f (k * g * k') = f g) →
    GlobalTheory.LKLoc.twOrbU (MonoidHom.id (GL ι K)) K0 γ (GlobalTheory.BCT.twCent (MonoidHom.id (GL ι K)) γ ⊓ K1) f = 0

def IwahoriRegularSeparable : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (ϖ : kˣ),
  ValuativeRel.valuation k (ϖ : k) = ValuativeRel.uniformizer k →
  ∀ ν : Fin N → ℤ, StrictAnti ν → ∀ x ∈ GlobalTheory.SmGL.iwahori k (Fin N), ∀ y ∈ GlobalTheory.SmGL.iwahori k (Fin N),
    let g := x * GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ ν * y
    (g : Matrix (Fin N) (Fin N) k).charpoly.Separable ∧ (g : Matrix (Fin N) (Fin N) k).charpoly.Splits

def CoefCusp : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
  (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), GlobalTheory.SmGL.IsCuspidal π →
  ∀ (v : V), ∀ l ∈ smoothPart π.dual,
  ∀ f : GL (Fin N) k → ℂ, (∀ g, f g = if ValuativeRel.valuation k (g : Matrix (Fin N) (Fin N) k).det = 1 then l (π g v) else 0) →
  IsLocallyConstant f ∧ HasCompactSupport f ∧
  ∃ K0 : Subgroup (GL (Fin N) k), IsOpen (K0 : Set (GL (Fin N) k)) ∧ IsCompact (K0 : Set (GL (Fin N) k)) ∧
    (∀ x ∈ K0, ∀ y ∈ K0, ∀ g, f (x * g * y) = f g) ∧
  (∀ (a b : ℕ) (e : Fin N ≃ Fin a ⊕ Fin b), 0 < a → 0 < b → ∀ (μ : Measure (Fin a → Fin b → k)), μ.IsAddHaarMeasure →
    ∀ u : (Fin a → Fin b → k) → GL (Fin N) k,
      (∀ X, (u X : Matrix (Fin N) (Fin N) k) = Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) →
      ∀ g h : GL (Fin N) k, ∫ X, f (g * (h⁻¹ * u X * h)) ∂μ = 0)

def TypeCusp : Prop :=
  ∀ (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (ι : Type) [Fintype ι] [DecidableEq ι] (J : Subgroup (GL ι K)), IsOpen (J : Set (GL ι K)) → IsCompact (J : Set (GL ι K)) →
  ∀ χ : J →* ℂˣ, IsOpen (χ.ker : Set J) →
  (∀ (a b : ℕ) (e : ι ≃ Fin a ⊕ Fin b), 0 < a → 0 < b → ∀ u : (Fin a → Fin b → K) → GL ι K,
      (∀ X, (u X : Matrix ι ι K) = Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) →
      ∀ h : GL ι K, ∃ X, ∃ hX : h⁻¹ * u X * h ∈ J, χ ⟨_, hX⟩ ≠ 1) →
  ∀ f : GL ι K → ℂ, (∀ g (hg : g ∈ J), f g = (((χ ⟨g, hg⟩)⁻¹ : ℂˣ) : ℂ)) → (∀ g, g ∉ J → f g = 0) →
  IsLocallyConstant f ∧ HasCompactSupport f ∧
  (∀ x ∈ (χ.ker.map J.subtype), ∀ y ∈ (χ.ker.map J.subtype), ∀ g, f (x * g * y) = f g) ∧
  (∀ (a b : ℕ) (e : ι ≃ Fin a ⊕ Fin b), 0 < a → 0 < b → ∀ (μ : Measure (Fin a → Fin b → K)), μ.IsAddHaarMeasure →
    ∀ u : (Fin a → Fin b → K) → GL ι K,
      (∀ X, (u X : Matrix ι ι K) = Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) →
      ∀ g h : GL ι K, ∫ X, f (g * (h⁻¹ * u X * h)) ∂μ = 0)

def Top : Prop :=
  GlobalTheory.LKDef.TraceDefinitePairsEqAutomorphicTrace ∧ FinTF ∧ FinTFOrb ∧ CuspOrbZero ∧ IwahoriRegularSeparable ∧ CoefCusp ∧ TypeCusp

end GlobalTheory.Block5c
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.NotCoinvQuotEmpty
section
noncomputable section

open GlobalTheory.WeilM GlobalTheory.Published.HoweDualityFiniteModel
open scoped Matrix

namespace GlobalTheory.LinPair.Model

section General

variable {k : Type} [Field k] [Invertible (2 : k)] {E : Type} [Field E] [Algebra k E] {c : E →ₐ[k] E}
  {α β ν κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ν] [DecidableEq ν] [Fintype κ]
  [TopologicalSpace k] [IsTopologicalRing k] [LocallyCompactSpace k] [TopologicalSpace E] [IsModuleTopology k E]
  {ψ : AddChar k ℂ} {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {d : Darboux (symp c ξ JA JB) κ} {χ : Eˣ →* Circle}
  {Cy : Matrix β ν E} {om : UG c JA × UG c JB →* Module.End ℂ ((κ → k) → ℂ)} {l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ}

theorem comm {G H Y : Type} [Group G] [Group H] (om : G × H →* Module.End ℂ (Y → ℂ)) (g : G) (h : H) (φ : Y → ℂ) :
    om (1, h) (om (g, 1) φ) = om (g, 1) (om (1, h) φ) := by
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]; simp

theorem locAug_le_ker (h : IsLinPair c ψ ξ JA JB d χ Cy om) (hl : IsYInv c ψ d Cy l) :
    locAug om ≤ LinearMap.ker (secMap om l) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g, φ, hφ, rfl⟩
  refine LinearMap.mem_ker.2 (funext fun x => ?_)
  rw [map_sub, Pi.sub_apply, secMap_apply, secMap_apply, comm, h.lin l hl g (om (1, x) φ) (h.split.2.1.pres x φ hφ)]
  simp

theorem locAug_le_SB (h : IsLinPair c ψ ξ JA JB d χ Cy om) : locAug om ≤ SB (κ → k) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g, φ, hφ, rfl⟩
  exact (SB _).sub_mem (h.pres g φ hφ) hφ

theorem locAug_ne_SB (h : IsLinPair c ψ ξ JA JB d χ Cy om) (hl : IsYForm c ψ d Cy l) : locAug om ≠ SB (κ → k) := by
  intro e
  obtain ⟨φ, hφ, h0⟩ := hl.2
  have := congrFun (LinearMap.mem_ker.1 (locAug_le_ker h hl.1 (e ▸ hφ))) 1
  rw [secMap_apply, show ((1 : UG c JA), (1 : UG c JB)) = 1 from rfl, map_one] at this
  exact h0 this

theorem sec_left (h : IsLinPair c ψ ξ JA JB d χ Cy om) (hl : IsYInv c ψ d Cy l) {f : UG c JB → ℂ} (hf : f ∈ secSpace om l)
    (p : UG c JB) (t : GL ν E) (hp : ((p : GL β E) : Matrix β β E) * Cy = Cy * (t : Matrix ν ν E)) (x : UG c JB) :
    f (p * x) = (χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
      (((MeasureTheory.distribHaarChar k (Units.map (Algebra.norm k : E →* k) (Matrix.GeneralLinearGroup.det t)) : ℝ) ^
        ((Fintype.card α : ℝ) / 2) : ℝ) : ℂ) * f x := by
  obtain ⟨φ, hφ, rfl⟩ := hf
  have := h.split.2.2 l trivial hl p t hp _ (h.split.2.1.pres x φ hφ)
  rw [secMap_apply, secMap_apply, show ((1 : UG c JA), p * x) = (1, p) * (1, x) by simp, map_mul]
  exact this

theorem sec_right (h : IsLinPair c ψ ξ JA JB d χ Cy om) {f : UG c JB → ℂ} (hf : f ∈ secSpace om l) (y : UG c JB) :
    (fun x => f (x * y)) ∈ secSpace om l := by
  obtain ⟨φ, hφ, rfl⟩ := hf
  refine ⟨om (1, y) φ, h.split.2.1.pres y φ hφ, funext fun x => ?_⟩
  rw [secMap_apply, secMap_apply, show ((1 : UG c JA), x * y) = (1, x) * (1, y) by simp, map_mul]
  rfl

omit [IsTopologicalRing k] [LocallyCompactSpace k] [TopologicalSpace E] [IsModuleTopology k E] [DecidableEq α]
  [DecidableEq β] [DecidableEq ν] in

theorem isYInv_eval_zero (hd : ∀ z : Matrix α ν E, (d.e (z * Cyᵀ)).1 = 0) :
    IsYInv c ψ d Cy (LinearMap.proj (0 : κ → k)) := by
  intro z φ _
  simp [Darboux.rho, schr, hd]

end General

section Abstract

theorem SB_top (Y : Type) [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y] : SB Y = ⊤ :=
  eq_top_iff.2 fun _ _ => ⟨IsLocallyConstant.of_discrete _, HasCompactSupport.of_compactSpace _⟩

theorem locAug_one (G H Y : Type) [Group G] [Group H] [TopologicalSpace Y] :
    locAug (1 : G × H →* Module.End ℂ (Y → ℂ)) = ⊥ := by
  refine le_bot_iff.1 (Submodule.span_le.2 ?_)
  rintro _ ⟨g, φ, -, rfl⟩
  simp

theorem coinvQuot_point (G G' H Y Y' : Type) [Group G] [Group G'] [Group H] [TopologicalSpace Y] [DiscreteTopology Y]
    [Finite Y] [Nonempty Y] [TopologicalSpace Y'] [Unique Y'] :
    IsCoinvQuot (1 : G × H →* Module.End ℂ (Y → ℂ)) (1 : G' × H →* Module.End ℂ (Y' → ℂ)) := by
  have hf : Module.finrank ℂ (Y' → ℂ) = 1 := by rw [Module.finrank_fintype_fun_eq_card]; simp
  haveI : IsSimpleOrder (Submodule ℂ (Y' → ℂ)) := is_simple_module_of_finrank_eq_one hf
  obtain ⟨y⟩ := ‹Nonempty Y›
  refine ⟨?_, fun N _ _ _ => ?_, (locAug 1).mkQ ∘ₗ LinearMap.funLeft ℂ ℂ (fun _ => y), ?_, ?_, fun h φ _ φ' _ e => e⟩
  · rw [locAug_one, SB_top]; exact bot_ne_top
  · rw [locAug_one, SB_top]; exact eq_bot_or_eq_top N
  · rw [Submodule.map_comp, SB_top, SB_top, Submodule.map_top (LinearMap.funLeft ℂ ℂ _), LinearMap.range_eq_top.2]
    exact fun f => ⟨fun _ => f default, funext fun z => by simp [LinearMap.funLeft, Subsingleton.elim z default]⟩
  · rw [locAug_one]; exact bot_le

theorem not_coinvQuot_two {G Y : Type} [Group G] [TopologicalSpace Y] (om : G × Unit →* Module.End ℂ (Y → ℂ)) :
    ¬ IsCoinvQuot om (1 : Unit × Unit →* Module.End ℂ (Bool → ℂ)) := by
  rintro ⟨-, h, -⟩
  rw [locAug_one, SB_top] at h
  rcases h (LinearMap.ker (LinearMap.proj true)) bot_le le_top (fun _ _ h => h) with e | e
  · have : (Pi.single false 1 : Bool → ℂ) ∈ LinearMap.ker (LinearMap.proj (R := ℂ) (φ := fun _ : Bool => ℂ) true) := by simp
    rw [e] at this
    simpa using congrFun ((Submodule.mem_bot ℂ).1 this) false
  · have : (1 : Bool → ℂ) ∈ LinearMap.ker (LinearMap.proj (R := ℂ) (φ := fun _ : Bool => ℂ) true) := e ▸ trivial
    simp at this

theorem not_coinvQuot_empty {G G' H Y' : Type} [Group G] [Group G'] [Group H] [TopologicalSpace Y']
    (om : G × H →* Module.End ℂ (Empty → ℂ)) (om' : G' × H →* Module.End ℂ (Y' → ℂ)) (hle : locAug om' ≤ SB Y') :
    ¬ IsCoinvQuot om om' := by
  rintro ⟨h0, -, p, hp, -⟩
  refine h0 (le_antisymm hle fun φ hφ => ?_)
  obtain ⟨z, -, hz⟩ : (locAug om').mkQ φ ∈ (SB Empty).map p := hp ▸ ⟨φ, hφ, rfl⟩
  rw [Subsingleton.elim z 0, map_zero] at hz
  exact (Submodule.Quotient.mk_eq_zero _).1 hz.symm

theorem not_coinvQuot_sign (om : Unit × ℂˣ →* Module.End ℂ (Unit → ℂ)) (hom : ∀ u φ, om (1, u) φ = (u : ℂ) • φ) :
    ¬ IsCoinvQuot om (1 : Unit × ℂˣ →* Module.End ℂ (Unit → ℂ)) := by
  rintro ⟨-, -, p, hp, -, he⟩
  rw [SB_top] at hp he
  obtain ⟨z, -, hz⟩ : (locAug 1).mkQ (1 : Unit → ℂ) ∈ (⊤ : Submodule ℂ (Unit → ℂ)).map p := hp ▸ ⟨1, trivial, rfl⟩
  have := he (-1) z trivial 1 trivial hz
  rw [hom, map_smul, hz, ← map_smul] at this
  have h2 := (Submodule.Quotient.eq _).1 this
  rw [locAug_one] at h2
  have := congrFun ((Submodule.mem_bot ℂ).1 h2) ()
  simp at this
  norm_num at this

end Abstract

section Witt

variable {k E : Type} [Field k] [Field E] [Algebra k E] (c : E →ₐ[k] E)

theorem wittStep_plane : IsWittStep c 1 (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) E) (1 : Matrix (Fin 0) (Fin 0) E) := by
  refine ⟨rfl, Matrix.of fun i j => Sum.elim (fun x => x.elim0) (Sum.elim (fun _ => if i = 0 then 1 else 0)
    (fun _ => if i = 1 then 1 else 0)) j, ?_⟩
  ext (i | i | i) (j | j | j) <;> first | exact i.elim0 | exact j.elim0 |
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Subsingleton.elim i j]

theorem not_wittStep_aniso {a a' r : ℕ} (hr : 0 < r) (JA : Matrix (Fin a) (Fin a) E) (JA' : Matrix (Fin a') (Fin a') E)
    (h : ∀ x : Fin a → E, x ⬝ᵥ JA *ᵥ (c ∘ x) = 0 → x = 0) : ¬ IsWittStep c r JA JA' := by
  rintro ⟨-, P, hP⟩
  let i : Fin r := ⟨0, hr⟩
  have key : ∀ u v, (fun s => P s u) ⬝ᵥ JA *ᵥ (c ∘ fun s => P s v) = (Pᵀ * JA * P.map c) u v := fun u v => by
    rw [Matrix.mul_assoc]; rfl
  have h1 := h (fun s => P s (.inr (.inl i))) (by rw [key, hP]; simp)
  have h2 := key (.inr (.inl i)) (.inr (.inr i))
  rw [h1, hP] at h2
  simp at h2

end Witt

section RankZero

variable {k : Type} [Field k] [Invertible (2 : k)] {E : Type} [Field E] [Algebra k E] (c : E →ₐ[k] E)

omit [Invertible (2 : k)] in
theorem lagr_plane : IsLagr c (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) E) (!![1; 0] : Matrix (Fin 2) (Fin 1) E) := by
  refine ⟨?_, !![0; 1], Matrix.fromRows !![1, 0] !![0, 1], ?_, ?_, ?_⟩
  · ext i j; simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  · ext i j; simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fintype.sum_sum_type]
  · ext (i | i) (j | j) <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Subsingleton.elim i j]

variable [TopologicalSpace k] [IsTopologicalRing k] [LocallyCompactSpace k] [TopologicalSpace E] [IsModuleTopology k E]

theorem linPair_one (ψ : AddChar k ℂ) (ξ : E) (JA : Matrix (Fin 0) (Fin 0) E) {β ν : Type} [Fintype β] [DecidableEq β]
    [Fintype ν] [DecidableEq ν] (JB : Matrix β β E) (Cy : Matrix β ν E) (hL : IsLagr c JB Cy)
    (co : Darboux (symp c ξ JA JB) Empty) : IsLinPair c ψ ξ JA JB co 1 Cy 1 := by
  refine ⟨⟨hL, ?_, fun l _ _ p t hp φ _ => by simp⟩, fun _ _ h => h, fun g w φ _ => ?_, fun _ _ _ _ _ => rfl⟩
  · rw [MonoidHom.one_comp]; exact split_one ψ _
  · rw [Subsingleton.elim (_ * w) w]; rfl

def RankZero (ψ : AddChar k ℂ) : Prop :=
  ∃ (JA : Matrix (Fin 0) (Fin 0) E) (JB : Matrix (Fin 2) (Fin 2) E) (Cy : Matrix (Fin 2) (Fin 1) E)
    (co : Darboux (symp c (-1) JA JB) Empty) (om : UG c JA × UG c JB →* Module.End ℂ ((Empty → k) → ℂ))
    (l : ((Empty → k) → ℂ) →ₗ[ℂ] ℂ),
    IsHerm c JA ∧ (∀ i j, c (JB j i) = -JB i j) ∧
    JB.det ≠ 0 ∧ IsLagr c JB Cy ∧ IsLinPair c ψ (-1) JA JB co 1 Cy om ∧ IsUWeilPair c (sbClass k) ψ (-1) JA JB co 1 1 om ∧
    IsYForm c ψ co Cy l ∧ IsCoinvQuot om om

theorem rankZero (ψ : AddChar k ℂ) : RankZero c ψ := by
  refine ⟨1, !![0, 1; -1, 0], !![1; 0], GlobalTheory.WeilM.SiegelModel.darbZero _ _ _ _, 1, LinearMap.proj 0,
    ⟨fun i => i.elim0, by simp⟩, fun i j => by fin_cases i <;> fin_cases j <;> simp, by simp, lagr_plane c,
    linPair_one c ψ _ _ _ _ (lagr_plane c) _,
    ⟨weilB_one ψ _, ⟨GlobalTheory.WeilM.SiegelModel.darbZero _ _ _ _, fun _ => Subsingleton.elim _ _, weilB_one ψ _⟩,
      fun l _ φ _ => continuous_const (y := l φ)⟩,
    ⟨isYInv_eval_zero fun _ => Subsingleton.elim _ _, 1, ?_, ?_⟩, ?_⟩
  · exact ⟨IsLocallyConstant.const 1, HasCompactSupport.of_compactSpace _⟩
  · exact one_ne_zero
  · exact coinvQuot_point _ _ _ _ _

end RankZero

theorem rankZero_sqrt (K : Type) [Field K] [CharZero K] [Invertible (2 : K)] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (e : K) [Fact (∀ r : K, r ^ 2 ≠ e + 0 * r)] :
    ∃ (_ : TopologicalSpace (QuadraticAlgebra K e 0)) (_ : IsModuleTopology K (QuadraticAlgebra K e 0))
      (c : QuadraticAlgebra K e 0 →ₐ[K] QuadraticAlgebra K e 0) (δ : QuadraticAlgebra K e 0) (ψ : AddChar K ℂ),
      IsQuad c δ ∧ Continuous ψ ∧ (∀ t, ‖ψ t‖ = 1) ∧ ψ ≠ 1 ∧ RankZero c ψ := by
  obtain ⟨t, m, c, δ, -, ψ, -, hq, -, h1, h2, h3, -, -⟩ := GlobalTheory.SplitUnitary.Model.isQuad_isHerm_continuous_resEtaPow K e 0
  exact ⟨t, m, c, δ, ψ, hq, h1, h2, h3, rankZero c ψ⟩

end GlobalTheory.LinPair.Model

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.Rank1
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec

namespace GlobalTheory.ResW

def Rank1 : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) (V : Submodule ℂ (Sm E N)) (B : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ) (u : List (Letter E)) (x : Letter E) (t : ℝ), IsSquareIntegrableAutomorphicSpace V → SatFam V B → HasWord V u → rexp x = 0 → u.Perm [tw x (-t), tw x t] → t < 1

end GlobalTheory.ResW

end
end


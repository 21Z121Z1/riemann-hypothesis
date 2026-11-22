import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsGLSubmatrix
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints

open GlobalTheory.Grid GlobalTheory.Doubling

variable {D : D7}

def adj (S T : HSp D) (y : WO S T) : WO T S :=
  HMul.hMul (HMul.hMul ((S.gram⁻¹).map (incA D)) ((y : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D)).transpose)
    (T.gram.map (incA D))

def blkL (M V V₁ : HSp D) (z : WO M (hsum V V₁)) : WO M V := fun a b => z (Fin.castAdd V₁.rank a) b

def blkR (M V V₁ : HSp D) (z : WO M (hsum V V₁)) : WO M V₁ := fun a b => z (Fin.natAdd V.rank a) b

def ten (M V V₁ : HSp D) : (WO M V → ℂ) →ₗ[ℂ] (WO V₁ M → ℂ) →ₗ[ℂ] (WO M (hsum V V₁) → ℂ) :=
  LinearMap.mk₂ ℂ (fun φ φ' z => φ (blkL M V V₁ z) * φ' (adj M V₁ (blkR M V V₁ z)))
    (fun _ _ _ => funext fun _ => add_mul _ _ _) (fun _ _ _ => funext fun _ => mul_assoc _ _ _)
    (fun _ _ _ => funext fun _ => mul_add _ _ _) (fun _ _ _ => funext fun _ => mul_left_comm _ _ _)

section Route

variable (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (ε : Bool) (V M V₁ : Node D)

abbrev Pair : Type := (WO M.V V.V → ℂ) × (WO V₁.V M.V → ℂ)

abbrev RealPart : Type := Pol M V ⊗[ℂ] Pol V₁ M

def IsFinPair (f : Pair V M V₁) : Prop := IsFinVec ψ θ ε M V f.1 ∧ IsFinVec ψ θ (!ε) V₁ M f.2

def IsAlgPair (φ : Pair V M V₁) : Prop :=
  ∃ f, IsFinPair ψ θ ε V M V₁ f ∧ ∃ P P', φ = (fock ψ θ ε M V f.1 P, fock ψ θ (!ε) V₁ M f.2 P')

def total {n : ℕ} (Φ : Fin n → Pair V M V₁) : WO M.V (hsum V.V V₁.V) → ℂ := ∑ k, ten M.V V.V V₁.V (Φ k).1 (Φ k).2

def algVec : Submodule ℂ (WO M.V (hsum V.V V₁.V) → ℂ) :=
  Submodule.span ℂ {Φ | ∃ φ, IsAlgPair ψ θ ε V M V₁ φ ∧ Φ = ten M.V V.V V₁.V φ.1 φ.2}

def withFin (f : Pair V M V₁) : RealPart V M V₁ →ₗ[ℂ] (WO M.V (hsum V.V V₁.V) → ℂ) :=
  TensorProduct.lift (ten M.V V.V V₁.V) ∘ₗ TensorProduct.map (fock ψ θ ε M V f.1) (fock ψ θ (!ε) V₁ M f.2)

variable {V M V₁}

def route (a : ArrS M V) (b : ArrS V₁ M) (mV : V.MeasDat) (mM : M.MeasDat) {n : ℕ} (Φ : Fin n → Pair V M V₁)
    (F : GA D V.V → ℂ) : GA D V₁.V → ℂ :=
  ∑ k, b.int mM (Φ k).2 (a.int mV (Φ k).1 F)

end Route

section Quot

variable (θ : InfFam D)

def IsDer (X : HSp D) {Z : Type} (ρ : GA D X → Module.End ℂ (Z → ℂ)) (τ : D.what₂.Tau) (Y : Matrix (Fin X.rank) (Fin X.rank) ℂ)
    (Φ Φ' : Z → ℂ) : Prop :=
  ∀ z, HasDerivAt (fun t : ℝ => ρ (oneP θ X τ Y t) Φ z) (Φ' z) 0

def IsStable (X : HSp D) {Z : Type} (ρ : GA D X → Module.End ℂ (Z → ℂ)) (S : Submodule ℂ (Z → ℂ)) : Prop :=
  (∀ g ∈ GfC X, ∀ Φ ∈ S, ρ g Φ ∈ S) ∧ ∀ τ, ∀ Y ∈ lieAt X τ, ∀ Φ ∈ S, ∃ Φ' ∈ S, IsDer θ X ρ τ Y Φ Φ'

def IsIrred (X : HSp D) (Pi : ModuleCat.{0} ℂ) (rf : GA D X → Module.End ℂ Pi)
    (rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi) : Prop :=
  Nontrivial Pi ∧ ∀ N : Submodule ℂ Pi, (∀ g ∈ GfC X, ∀ x ∈ N, rf g x ∈ N) → (∀ τ, ∀ Y ∈ lieAt X τ, ∀ x ∈ N, rl τ Y x ∈ N) →
    N = ⊥ ∨ N = ⊤

structure IsCoinvMap {M X : HSp D} (ω : WRep M X) (S : Submodule ℂ (WO M X → ℂ)) (Pi : ModuleCat.{0} ℂ)
    (rf : GA D X → Module.End ℂ Pi) (rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi)
    (p : (WO M X → ℂ) →ₗ[ℂ] Pi) : Prop where

  stabM : IsStable θ M (fun g => ω (g, 1)) S

  stabX : IsStable θ X (fun h => ω (1, h)) S

  onto : S.map p = ⊤

  invf : ∀ g ∈ GfC M, ∀ Φ ∈ S, p (ω (g, 1) Φ) = p Φ

  invl : ∀ τ, ∀ Y ∈ lieAt M τ, ∀ Φ ∈ S, ∀ Φ' ∈ S, IsDer θ M (fun g => ω (g, 1)) τ Y Φ Φ' → p Φ' = 0

  eqf : ∀ h ∈ GfC X, ∀ Φ ∈ S, p (ω (1, h) Φ) = rf h (p Φ)

  eql : ∀ τ, ∀ Y ∈ lieAt X τ, ∀ Φ ∈ S, ∀ Φ' ∈ S, IsDer θ X (fun h => ω (1, h)) τ Y Φ Φ' → p Φ' = rl τ Y (p Φ)

end Quot

variable {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (G : GridDat R)

abbrev big (i j : ℕ) : HSp D := hsum (G.V i (j + 1)).V (G.V (i + 1) j).V

variable (R) in

def al (t : T) (i j : ℕ) : (AE D)ˣ →* Circle := R.toLevCh.mu t (j + 1) * R.eta ^ (rkV D i j % 2)

def be (i j : ℕ) : (AE D)ˣ →* Circle := G.chi (D.R.m - i) * R.eta ^ (rkV D i j % 2)

structure IsMatching (t : T) (i j : ℕ) (ωA : WRep (G.V (i + 1) (j + 1)).V (big G i j)) (ωB : WRep (G.V i j).V (big G i j))
    (Pi : ModuleCat.{0} ℂ) (rf : GA D (big G i j) → Module.End ℂ Pi)
    (rl : D.what₂.Tau → Matrix (Fin (big G i j).rank) (Fin (big G i j).rank) ℂ → Module.End ℂ Pi)
    (p : (WO (G.V (i + 1) (j + 1)).V (big G i j) → ℂ) →ₗ[ℂ] Pi) (p' : (WO (G.V i j).V (big G i j) → ℂ) →ₗ[ℂ] Pi) : Prop where

  weilA : IsWeil R.ψ true (G.V (i + 1) (j + 1)).V (big G i j) (be G i j) (be G i j / al R t i j) ωA

  weilB : IsWeil R.ψ false (G.V i j).V (big G i j) (al R t i j) (al R t i j / be G i j) ωB

  irred : IsIrred (big G i j) Pi rf rl

  mapA : IsCoinvMap R.θ ωA (algVec R.ψ R.θ true (G.V i (j + 1)) (G.V (i + 1) (j + 1)) (G.V (i + 1) j)) Pi rf rl p

  mapB : IsCoinvMap R.θ ωB (algVec R.ψ R.θ false (G.V i (j + 1)) (G.V i j) (G.V (i + 1) j)) Pi rf rl p'

def routeA (t : T) (i j : ℕ) {n : ℕ} (Φ : Fin n → Pair (G.V i (j + 1)) (G.V (i + 1) (j + 1)) (G.V (i + 1) j))
    (F : GA D (G.V i (j + 1)).V → ℂ) : GA D (G.V (i + 1) j).V → ℂ :=
  route (G.X i (j + 1)) (G.th t (i + 1) j) (G.meas t i (j + 1)) (G.meas t (i + 1) (j + 1)) Φ F

def routeB (t : T) (i j : ℕ) {n : ℕ} (Φ : Fin n → Pair (G.V i (j + 1)) (G.V i j) (G.V (i + 1) j))
    (F : GA D (G.V i (j + 1)).V → ℂ) : GA D (G.V (i + 1) j).V → ℂ :=
  route (G.th t i j) (G.X i j) (G.meas t i (j + 1)) (G.meas t i j) Φ F

def CommWith (t : T) (i j : ℕ) {Pi : ModuleCat.{0} ℂ} (p : (WO (G.V (i + 1) (j + 1)).V (big G i j) → ℂ) →ₗ[ℂ] Pi)
    (p' : (WO (G.V i j).V (big G i j) → ℂ) →ₗ[ℂ] Pi) (c : ℂ) : Prop :=
  ∀ (n n' : ℕ) (ΦA : Fin n → Pair (G.V i (j + 1)) (G.V (i + 1) (j + 1)) (G.V (i + 1) j))
    (ΦB : Fin n' → Pair (G.V i (j + 1)) (G.V i j) (G.V (i + 1) j)),
    (∀ k, IsAlgPair R.ψ R.θ true _ _ _ (ΦA k)) → (∀ k, IsAlgPair R.ψ R.θ false _ _ _ (ΦB k)) →
    p (total _ _ _ ΦA) = p' (total _ _ _ ΦB) →
    ∀ (F : G.CV i (j + 1)) (v : SmT (G.V i (j + 1)).M), routeA G t i j ΦA (F.1 v) = c • routeB G t i j ΦB (F.1 v)

def MatchedExist (i j : ℕ) {Pi : ModuleCat.{0} ℂ} (p : (WO (G.V (i + 1) (j + 1)).V (big G i j) → ℂ) →ₗ[ℂ] Pi)
    (p' : (WO (G.V i j).V (big G i j) → ℂ) →ₗ[ℂ] Pi)
    (σ : RealPart (G.V i (j + 1)) (G.V i j) (G.V (i + 1) j) →ₗ[ℂ]
      RealPart (G.V i (j + 1)) (G.V (i + 1) (j + 1)) (G.V (i + 1) j)) : Prop :=
  ∀ fB, IsFinPair R.ψ R.θ false (G.V i (j + 1)) (G.V i j) (G.V (i + 1) j) fB →
    ∃ (n : ℕ) (fA : Fin n → Pair (G.V i (j + 1)) (G.V (i + 1) (j + 1)) (G.V (i + 1) j)),
      (∀ k, IsFinPair R.ψ R.θ true _ _ _ (fA k)) ∧
      ∀ Q, p (∑ k, withFin R.ψ R.θ true _ _ _ (fA k) (σ Q)) = p' (withFin R.ψ R.θ false _ _ _ fB Q)

def SquareComm (i j : ℕ) : Prop :=
  ∃ σ, ∀ t : T, (∃ ωA ωB Pi rf rl p p', IsMatching G t i j ωA ωB Pi rf rl p p') ∧
    ∀ ωA ωB Pi rf rl p p', IsMatching G t i j ωA ωB Pi rf rl p p' →
      (∃ c : ℂ, c ≠ 0 ∧ CommWith G t i j p p' c) ∧ MatchedExist G i j p p' σ

def SquaresCommute (F : Face D A) : Prop :=
  R.Char F → G.Is → ∀ i j, i < D.R.m → j < D.R.m → SquareComm G i j

example (t : T) (i j : ℕ) : al R t i j / be G i j = R.toLevCh.mu t (j + 1) / G.chi (D.R.m - i) :=
  mul_div_mul_right_eq_div _ _ _

example (M V V₁ : HSp D) (φ : WO M V → ℂ) (φ' : WO V₁ M → ℂ) : ten M V V₁ φ φ' 0 = φ 0 * φ' 0 := by
  have h : adj M V₁ (blkR M V V₁ 0) = 0 := by
    ext a b
    simp [adj, blkR, Matrix.mul_apply]
  show φ (blkL M V V₁ 0) * φ' (adj M V₁ (blkR M V V₁ 0)) = _
  rw [h]; rfl

example (hG : G.Is) (t : T) {i j : ℕ} (hi : i < D.R.m) (hj : j < D.R.m) (f : Pair (G.V i (j + 1)) (G.V (i + 1) (j + 1)) (G.V (i + 1) j))
    (hf : IsFinPair R.ψ R.θ true _ _ _ f) (P P') (F : G.CV i (j + 1)) (v : SmT (G.V i (j + 1)).M) :
    routeA G t i j (fun _ : Fin 1 => (fock R.ψ R.θ true _ _ f.1 P, fock R.ψ R.θ false _ _ f.2 P')) (F.1 v) =
      (G.ioT t (i + 1) j f.2 (G.ioX t i (j + 1) f.1 F)).1 ((G.th t (i + 1) j).It P' ((G.X i (j + 1)).It P v)) := by
  rw [routeA, route, Fin.sum_univ_one, (hG.lifts.X t i (j + 1) hi hj f.1 hf.1).int_eq]
  exact (hG.lifts.th t (i + 1) j hi hj f.2 hf.2).int_eq _ _ _

end GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SimplePoleTwistedLift
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift

open scoped TensorProduct Topology
open NumberField IsDedekindDomain Filter GlobalTheory.LFun

section Defs

variable {K : Type} [Field K] [NumberField K]

def liftFam (c : Fam K) (m x : HeightOneSpectrum (𝓞 K) → ℂˣ) (t : ℕ) : Fam K :=
  twist c (x * m⁻¹) + segFam x t

def IsZetaCont (T : Set (HeightOneSpectrum (𝓞 K))) (Z : ℂ → ℂ) : Prop :=
  MeromorphicOn Z Set.univ ∧ ∀ s : ℂ, 1 < s.re → Z s = zetaOff T s

def HasSimplePole (Λ : ℂ → ℂ) (s₀ : ℂ) : Prop :=
  MeromorphicAt Λ s₀ ∧ meromorphicOrderAt Λ s₀ = ((-1 : ℤ) : WithTop ℤ) ∧
    ∃ ρ : ℂ, ρ ≠ 0 ∧ Tendsto (fun s => (s - s₀) * Λ s) (𝓝[≠] s₀) (𝓝 ρ)

end Defs

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def rhs (S : Set (HeightOneSpectrum (𝓞 F))) (c : Fam E) (m : HeightOneSpectrum (𝓞 E) → ℂˣ) (t : ℕ)
    (Z : ℂ → ℂ) (s : ℂ) : ℂ :=
  LSTw S c m s * ∏ i ∈ Finset.range t, Z (s + ((t : ℂ) - 1) / 2 - i)

def Hyp (S : Set (HeightOneSpectrum (𝓞 F))) (r t : ℕ) (c P : Fam E) (m x : HeightOneSpectrum (𝓞 E) → ℂˣ) : Prop :=
  S.Finite ∧ r + 5 ≤ t ∧
    ∀ w ∉ above E S, (c w).card = r ∧
      (∀ b ∈ c w, ‖(b : ℂ)‖ ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (((r : ℝ) - 1) / 2)) ∧
      ‖(m w : ℂ)‖ = 1 ∧ ‖(x w : ℂ)‖ = 1 ∧ P w = liftFam c m x t w

def Concl (S : Set (HeightOneSpectrum (𝓞 F))) (r t : ℕ) (c P : Fam E) (m x : HeightOneSpectrum (𝓞 E) → ℂˣ) :
    Prop :=
  (∀ s : ℂ, ((t : ℝ) + 1) / 2 < s.re →
    Converges (above E S) (twist P x⁻¹) s ∧
      (∀ i < t, Converges (above E S) (fun _ => {1}) (s + ((t : ℂ) - 1) / 2 - i)) ∧
      LSTw S P x s = rhs S c m t (zetaOff (above E S)) s) ∧
  ((∀ s : ℂ, ((r : ℝ) + 1) / 2 < s.re → Converges (above E S) (twist c m⁻¹) s ∧ LSTw S c m s ≠ 0) ∧
    DifferentiableOn ℂ (LSTw S c m) {s | ((r : ℝ) + 1) / 2 < s.re}) ∧
  (∃ Z, IsZetaCont (above E S) Z) ∧
  ∀ Z, IsZetaCont (above E S) Z →
    MeromorphicOn (rhs S c m t Z) {s | ((r : ℝ) + 1) / 2 < s.re} ∧
      ((r : ℝ) + 1) / 2 < ((1 + (t : ℂ)) / 2).re ∧
      (∀ s : ℂ, ((t : ℝ) + 1) / 2 < s.re → rhs S c m t Z s = LSTw S P x s) ∧
      HasSimplePole (rhs S c m t Z) ((1 + (t : ℂ)) / 2)

def SimplePole : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (S : Set (HeightOneSpectrum (𝓞 F))) (r t : ℕ) (c P : Fam E) (m x : HeightOneSpectrum (𝓞 E) → ℂˣ),
    Hyp S r t c P m x → Concl S r t c P m x

section Rep

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU

theorem SimplePole.rep (h : SimplePole) (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (L : Submodule (𝓞 E) (Fin n → E)) {Vl : HeightOneSpectrum (𝓞 F) → Type} [∀ v, AddCommGroup (Vl v)]
    [∀ v, Module ℂ (Vl v)] (π : ∀ v, Representation ℂ (GLoc σ J v) (Vl v))
    {S : Set (HeightOneSpectrum (𝓞 F))} (hS : S.Finite) {r t : ℕ} (ht : r + 5 ≤ t) {c : Fam E}
    (μ χ : (AF F ⊗[F] E)ˣ →* Circle)
    (hc : ∀ w ∉ above E S, (c w).card = r ∧
      ∀ b ∈ c w, ‖(b : ℂ)‖ ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (((r : ℝ) - 1) / 2))
    (hπ : ∀ w ∉ above E S, paramFam σ J L π w = liftFam c (val μ) (val χ) t w) :
    ∃ Λ : ℂ → ℂ, MeromorphicOn Λ {s | ((r : ℝ) + 1) / 2 < s.re} ∧
      (∀ s : ℂ, ((t : ℝ) + 1) / 2 < s.re → Λ s = LSRep σ J L S π (val χ) s) ∧
      HasSimplePole Λ ((1 + (t : ℂ)) / 2) := by
  obtain ⟨-, -, ⟨Z, hZ⟩, h4⟩ := h F E S r t c _ (val μ) (val χ)
    ⟨hS, ht, fun w hw => ⟨(hc w hw).1, (hc w hw).2, norm_val μ w, norm_val χ w, hπ w hw⟩⟩
  exact ⟨_, (h4 Z hZ).1, (h4 Z hZ).2.2.1, (h4 Z hZ).2.2.2⟩

end Rep

theorem twist_liftFam (c : Fam E) (m x : HeightOneSpectrum (𝓞 E) → ℂˣ) (t : ℕ) :
    twist (liftFam c m x t) x⁻¹ = twist c m⁻¹ + segFam 1 t := by
  rw [liftFam, twist_add, twist_twist, twist_segFam, inv_mul_cancel_left, inv_mul_cancel]

example : Hyp (F := F) (E := E) ∅ 1 7 (fun _ => {1}) (liftFam (fun _ => {1}) 1 1 7) 1 1 :=
  ⟨Set.finite_empty, by norm_num, fun w _ => by simp⟩

example : HasSimplePole (fun s => s⁻¹) 0 := by
  refine ⟨(MeromorphicAt.id 0).inv, ?_, 1, one_ne_zero, ?_⟩
  · have h : meromorphicOrderAt (id⁻¹ : ℂ → ℂ) 0 = -meromorphicOrderAt (id : ℂ → ℂ) 0 := meromorphicOrderAt_inv
    rw [meromorphicOrderAt_id] at h
    exact h
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [sub_zero, mul_inv_cancel₀ hs]

end GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalThetaInertPlace
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace

open Matrix Formalism.UG ValuativeRel
open scoped TensorProduct
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsUWeilPair)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.LFun (HasSatU)

def str (q : ℂˣ) (n : ℤ) : Multiset ℂˣ := (Multiset.range n.toNat).map fun j : ℕ => q ^ (2 * (j : ℤ) - (n - 1))

section Valued

variable (E : Type) [Field E] [Valued E (WithZero (Multiplicative ℤ))]

def nu (z : Circle) : Eˣ →* Circle :=
  (zpowersHom Circle z⁻¹).comp ((WithZero.unitsWithZeroEquiv (α := Multiplicative ℤ)).toMonoidHom.comp
    (Units.map (Valued.v : Valuation E (WithZero (Multiplicative ℤ))).toMonoidWithZeroHom.toMonoidHom))

def chi (n : ℕ) : Eˣ →* Circle := nu E (Circle.exp Real.pi ^ n)

variable {E}

variable {n : ℕ}

def IsSelfDualLat (c : E →+* E) (S : Matrix (Fin n) (Fin n) E) (L : Submodule (intL E) (Fin n → E)) : Prop :=
  L.FG ∧ Submodule.span E (L : Set (Fin n → E)) = ⊤ ∧
    ∀ x, x ∈ L ↔ ∀ y ∈ L, x ⬝ᵥ S *ᵥ (fun i => c (y i)) ∈ intL E

def IsHypFrame (c : E →+* E) (S : Matrix (Fin n) (Fin n) E) (L : Submodule (intL E) (Fin n → E)) (P : GL (Fin n) E) :
    Prop :=
  (∀ y : Fin n → E, P.1 *ᵥ y ∈ L ↔ ∀ i, y i ∈ intL E) ∧
    ∃ u : E, Valued.v u = 1 ∧ P.1ᵀ * S * P.1.map c = u • antiJ E n

end Valued

section Local

variable {F : Type} [Field F] {E : Type} [Field E] [Valued E (WithZero (Multiplicative ℤ))] [Algebra F E]
  (c : E →ₐ[F] E) {n : ℕ} {X : Type} [AddCommGroup X] [Module ℂ X]

def HasPh (ϖ : E) (q : ℕ) (s : E) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (intL E) (Fin n → E)) (z : ℂˣ)
    (π : Representation ℂ (UG c J) X) (Φ : Multiset ℂˣ) : Prop :=
  ∃ (P : GL (Fin n) E) (e : UG c J ≃* GU (c : E →+* E) n) (α : Fin (n / 2) → ℂˣ),
    IsHypFrame (c : E →+* E) (s • J) L P ∧ (∀ g, (e g : GL (Fin n) E) = P⁻¹ * (g : GL (Fin n) E) * P) ∧
      HasSatU ϖ q (π.comp e.symm.toMonoidHom) α ∧ Φ = (bcParam n α).map (z⁻¹ * ·)

end Local

def HomNeZero {G Y Z : Type} [Group G] [TopologicalSpace Y] [AddCommGroup Z] [Module ℂ Z]
    (om : G →* Module.End ℂ (Y → ℂ)) (ρ : Representation ℂ G Z) : Prop :=
  ∃ T : SB Y →ₗ[ℂ] Z, T ≠ 0 ∧ ∀ (g : G) (φ φ' : SB Y), (φ' : Y → ℂ) = om g φ → T φ' = ρ g (T φ)

section Res

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

def qU : ℂˣ := Units.mk0 ((Nat.card 𝓀[F] : ℕ) : ℂ) (Nat.cast_ne_zero.2 Nat.card_pos.ne')

variable {F} in

def IsUnramAdd (ϖ : F) (ψ : AddChar F ℂ) : Prop :=
  (∀ x ∈ 𝒪[F], ψ x = 1) ∧ ∃ x ∈ 𝒪[F], ψ (ϖ⁻¹ * x) ≠ 1

end Res

def SphericalThetaInert : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] [Invertible (2 : F)] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (E : Type) [Field E] [Valued E (WithZero (Multiplicative ℤ))] [Algebra F E] [IsModuleTopology F E]
    (c : E →ₐ[F] E) (ξ : E) (ϖ : Fˣ),
    IsQuad c ξ → IsUnramInv (algebraMap F E ϖ) (c : E →+* E) (Nat.card 𝓀[F]) →
    Odd (Nat.card 𝓀[F]) → 3 < Nat.card 𝓀[F] →
  ∀ ψ : AddChar F ℂ, IsUnramAdd (ϖ : F) ψ →
  ∀ (a b : ℕ), 2 ≤ a → 2 ≤ b →
  ∀ (JA : Matrix (Fin a) (Fin a) E) (JB : Matrix (Fin b) (Fin b) E), WeilM.IsHerm c JA → WeilM.IsHerm c JB →
  ∀ (LA : Submodule (intL E) (Fin a → E)) (LB : Submodule (intL E) (Fin b → E)),
    IsSelfDualLat (c : E →+* E) JA LA → IsSelfDualLat (c : E →+* E) (ξ • JB) LB →
  ∀ (κ : Type) [Fintype κ] (d : Darboux (symp c ξ JA JB) κ)
    (om : UG c JA × UG c JB →* Module.End ℂ ((κ → F) → ℂ)),
    IsUWeilPair c (sbClass F) ψ ξ JA JB d (chi E a) (chi E b) om →
  ∀ (X X' : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup X'] [Module ℂ X']
    (π : Representation ℂ (UG c JA) X) (π' : Representation ℂ (UG c JB) X'),
    π.IsIrreducible → GlobalTheory.PRep.IsSmooth π → π'.IsIrreducible → GlobalTheory.PRep.IsSmooth π' →
    HomNeZero om (extProd π π') →
  ∀ Φ Φ' : Multiset ℂˣ,
    HasPh c (algebraMap F E ϖ) (Nat.card 𝓀[F]) 1 JA LA
      (Circle.toUnits (chi E b (Units.map (algebraMap F E : F →* E) ϖ))) π Φ →
    HasPh c (algebraMap F E ϖ) (Nat.card 𝓀[F]) ξ JB LB
      (Circle.toUnits (chi E a (Units.map (algebraMap F E : F →* E) ϖ))) π' Φ' →
    Φ' + str (qU F) (-((b : ℤ) - a)) = Φ + str (qU F) ((b : ℤ) - a)

example (q : ℂˣ) : str q 1 = {1} ∧ str q 2 = {q, q⁻¹} := by
  constructor
  · simp [str]
  · have : Multiset.range (Int.toNat 2) = {1, 0} := by decide
    rw [str, this]
    simp

example {E : Type} [Field E] [Valued E (WithZero (Multiplicative ℤ))] (c : E →+* E) (n : ℕ) :
    IsHypFrame c (antiJ E n) (Submodule.pi Set.univ fun _ => (1 : Submodule (intL E) E)) 1 :=
  ⟨fun y => by
    simp only [Units.val_one, one_mulVec, Submodule.mem_pi, Set.mem_univ, forall_true_left, Submodule.mem_one]
    exact forall_congr' fun i => ⟨fun ⟨r, hr⟩ => hr ▸ r.2, fun h => ⟨⟨_, h⟩, rfl⟩⟩,
  1, map_one _, by simp [Matrix.map_one _ (map_zero c) (map_one c)]⟩

end GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TrivialParameterBound
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound

open Formalism.UG GlobalTheory.PRep GlobalTheory.LGrp GlobalTheory.LFun

def TrivialBound (q n : ℕ) (α : Fin (n / 2) → ℂˣ) : Prop :=
  ∀ i, ((q : ℝ) ^ 2) ^ (-(((n : ℝ) - 1) / 2)) ≤ ‖(α i : ℂ)‖ ∧ ‖(α i : ℂ)‖ ≤ ((q : ℝ) ^ 2) ^ (((n : ℝ) - 1) / 2)

def SatakeBoundInert : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ),
    IsUnramInv ϖ σ q →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GU σ n) V) (α : Fin (n / 2) → ℂˣ),
      IsIrrSmooth π → IsUnitarisable π → HasSatU ϖ q π α → TrivialBound q n α

def SatakeBoundInertPS : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ)
    (hU : IsUnramInv ϖ σ q) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GU σ n) V)
    (α : Fin (n / 2) → ℂˣ),
      (haveI := locallyCompact_GU_of_unram hU n; HasSatakeU π α) → IsUnitarisable π → TrivialBound q n α

theorem bound_eq (q n : ℕ) : ((q : ℝ) ^ 2) ^ (((n : ℝ) - 1) / 2) = (q : ℝ) ^ ((n : ℝ) - 1) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg q)]
  congr 1
  push_cast
  ring

def trivParam (q n : ℕ) (hq : q ≠ 0) : Fin (n / 2) → ℂˣ :=
  fun i => Units.mk0 (q : ℂ) (by exact_mod_cast hq) ^ ((n : ℤ) - 1 - 2 * (i.val : ℤ))

theorem trivial_hyp {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] {ϖ : L}
    {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (hq : q ≠ 0) (n : ℕ) :
    IsIrrSmooth (charRep (1 : GU σ n →* ℂˣ)) ∧ IsUnitarisable (charRep (1 : GU σ n →* ℂˣ)) ∧
      HasSatU ϖ q (charRep (1 : GU σ n →* ℂˣ)) (trivParam q n hq) := by
  have hc : ∀ b : GU σ n, chiDeltaU q (fun i => (trivParam q n hq i : ℂ)) b = 1 := fun b => by
    refine Finset.prod_eq_one fun i _ => ?_
    have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq
    split_ifs with h
    · simp only [trivParam, Units.val_zpow_eq_zpow_val, Units.val_mk0]
      rw [← zpow_mul, ← zpow_add₀ hq']
      convert zpow_zero (q : ℂ) using 2
      ring
    · rfl
  refine ⟨⟨fun z => by simp, charRep_irreducible _⟩, charRep_unitarisable _ (by simp), ?_, fun x _ h0 => ?_⟩
  · exact (Submodule.ne_bot_iff _).2 ⟨1, GlobalTheory.LGrp.mem_fixed.2 (by simp), one_ne_zero⟩
  · refine IsSatVecU.of_map hU (ρ' := rightReg ℂ _ ℂ) (LinearMap.pi fun _ => LinearMap.id)
      (fun g y => by funext z; simp [rightReg, LinearMap.funLeft]) (fun a b e => congrFun e 1)
      (isSatVecU_of_isSphericalU hU (fun b g k _ _ => by simp [hc]) fun e => h0 (congrFun e 1))

end GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound

end
end


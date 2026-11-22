import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1533
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1543
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1326
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1384
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0105
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceLatticeFractionalMultipleAgree
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0081
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1547
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0039
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleCharacterGoodIdempotentCuspidalProduc
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1548
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0508
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0067

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneOrthogonalGramRestriction
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

noncomputable section
namespace GlobalTheory.PlaneFrameCons
open Matrix
open Formalism.UG (cT)

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem gram_entry {n r s : ℕ} (σ : E →ₐ[F] E) (M : Matrix (Fin n) (Fin n) E) (A : Matrix (Fin n) (Fin r) E)
    (B : Matrix (Fin n) (Fin s) E) (i : Fin r) (j : Fin s) :
    (cT (σ : E →+* E) A * M * B) i j = hE σ M (fun k => A k i) (fun k => B k j) := by
  simp only [hE, Formalism.UG.hform, cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul,
    RingHom.coe_coe]
  rw [Finset.sum_comm]

theorem gram_mulVec_entry {n r : ℕ} (σ : E →ₐ[F] E) (M : Matrix (Fin n) (Fin n) E) (A : Matrix (Fin n) (Fin r) E)
    (z : Fin n → E) (i : Fin r) :
    ((cT (σ : E →+* E) A * M) *ᵥ z) i = hE σ M (fun k => A k i) z := by
  simp only [hE, Formalism.UG.hform, cT, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul, RingHom.coe_coe]
  rw [Finset.sum_comm]

variable [NumberField F] [NumberField E]

theorem hE_eq {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (c : E)
    (u v : Fin n → E) : hE σ (c • J.map σ) u v = c * σ (form σ J u v) := by
  have := GlobalTheory.TwoPlaneWitt.hE_smul_map hσ J c 1 1 u v
  simpa using this

theorem exists_isWittFrame_cons : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), (∀ i j, σ (W.J j i) = -W.J i j) → n = n₁ + 2 →
      form σ W.J H.x H.x = 0 → form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
      (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J → ∀ c₀ : E, c₀ ≠ 0 →
      IsHermND σ (c₀ • W₁.J.map σ) → IsHermND σ (c₀ • W.J.map σ) →
      ∀ (r : ℕ) (Xf Yf : Matrix (Fin n₁) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W₁.J.map σ) Xf Yf →
        ∃ X' Y' : Matrix (Fin n) (Fin (r + 1)) E, GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W.J.map σ) X' Y' ∧
          (∀ k, X' k 0 = H.x k) ∧ (∀ k, Y' k 0 = c₀⁻¹ * H.y k) ∧
          ∀ (k : Fin n) (i : Fin r), X' k i.succ = (H.ι * Xf) k i ∧ Y' k i.succ = (H.ι * Yf) k i := by
  intro F E _ _ _ _ _ σ hcm n n₁ W W₁ H hskew hn hxx hyy hxy horth hg c₀ hc hND₁ hND r Xf Yf hW
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hcm
  set M := c₀ • W.J.map σ with hM
  set M₁ := c₀ • W₁.J.map σ with hM₁

  have hι : ∀ u v, hE σ M (H.ι *ᵥ u) (H.ι *ᵥ v) = hE σ M₁ u v := fun u v => by
    rw [hM, hM₁, hE_eq hσ, hE_eq hσ, GlobalTheory.TwoPlaneWitt.form_mulVec, hg]
  have hcol : ∀ (A : Matrix (Fin n₁) (Fin r) E) (i : Fin r), (fun k => (H.ι * A) k i) = H.ι *ᵥ fun k => A k i :=
    fun A i => funext fun k => by simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hyx : form σ W.J H.y H.x = -1 := by rw [GlobalTheory.UnipCocptForm.form_swap σ W.J hskew hσ, hxy, map_one]
  have hxι : ∀ u, form σ W.J H.x (H.ι *ᵥ u) = 0 := fun u => by
    rw [GlobalTheory.UnipCocptForm.form_swap σ W.J hskew hσ, (horth u).1, map_zero, neg_zero]
  have hyι : ∀ u, form σ W.J H.y (H.ι *ᵥ u) = 0 := fun u => by
    rw [GlobalTheory.UnipCocptForm.form_swap σ W.J hskew hσ, (horth u).2, map_zero, neg_zero]
  let X' : Matrix (Fin n) (Fin (r + 1)) E := Matrix.of fun k => Fin.cons (H.x k) (fun i => (H.ι * Xf) k i)
  let Y' : Matrix (Fin n) (Fin (r + 1)) E := Matrix.of fun k => Fin.cons (c₀⁻¹ * H.y k) (fun i => (H.ι * Yf) k i)
  have cX0 : (fun k => X' k 0) = H.x := funext fun k => by simp [X']
  have cY0 : (fun k => Y' k 0) = c₀⁻¹ • H.y := funext fun k => by simp [Y']
  have cXs : ∀ i : Fin r, (fun k => X' k i.succ) = H.ι *ᵥ fun k => Xf k i := fun i => by
    rw [← hcol]; funext k; simp [X']
  have cYs : ∀ i : Fin r, (fun k => Y' k i.succ) = H.ι *ᵥ fun k => Yf k i := fun i => by
    rw [← hcol]; funext k; simp [Y']
  have gXX : ∀ i j, hE σ M₁ (fun k => Xf k i) (fun k => Xf k j) = 0 := fun i j => by
    rw [← gram_entry, hW.xx]; rfl
  have gYY : ∀ i j, hE σ M₁ (fun k => Yf k i) (fun k => Yf k j) = 0 := fun i j => by
    rw [← gram_entry, hW.yy]; rfl
  have gXY : ∀ i j, hE σ M₁ (fun k => Xf k i) (fun k => Yf k j) = (1 : Matrix (Fin r) (Fin r) E) i j := fun i j => by
    rw [← gram_entry, hW.xy]
  have sX : ∀ (s t : E) (a b : Fin n → E), hE σ M (s • a) (t • b) = σ s * t * c₀ * σ (form σ W.J a b) :=
    fun s t a b => GlobalTheory.TwoPlaneWitt.hE_smul_map hσ W.J c₀ s t a b
  refine ⟨X', Y', ⟨?_, ?_, ?_, ?_⟩, fun k => by simp [X'], fun k => by simp [Y'], fun k i => ⟨by simp [X'], by simp [Y']⟩⟩
  · ext i j
    rw [gram_entry]
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · rw [cX0, ← one_smul E H.x, sX]; simp [hxx]
    · rw [cX0, cXs, ← one_smul E H.x, ← one_smul E (H.ι *ᵥ _), sX]; simp [hxι]
    · rw [cX0, cXs, ← one_smul E H.x, ← one_smul E (H.ι *ᵥ _), sX]; simp [(horth _).1]
    · rw [cXs, cXs, hι, gXX]; rfl
  · ext i j
    rw [gram_entry]
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · rw [cY0, sX]; simp [hyy]
    · rw [cY0, cYs, ← one_smul E (H.ι *ᵥ _), sX]; simp [hyι]
    · rw [cY0, cYs, ← one_smul E (H.ι *ᵥ _), sX]; simp [(horth _).2]
    · rw [cYs, cYs, hι, gYY]; rfl
  · ext i j
    rw [gram_entry]
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · rw [cX0, cY0, ← one_smul E H.x, sX]; simp [hxy, hc]
    · rw [Matrix.one_apply_ne (Fin.succ_ne_zero j).symm, cX0, cYs, ← one_smul E H.x, ← one_smul E (H.ι *ᵥ _), sX]; simp [hxι]
    · rw [Matrix.one_apply_ne (Fin.succ_ne_zero i), cY0, cXs, ← one_smul E (H.ι *ᵥ _), sX]; simp [(horth _).2]
    · rw [cXs, cYs, hι, gXY]; simp [Matrix.one_apply]
  · intro z h1 h2 h3
    have σinj : ∀ a : E, σ a = 0 → a = 0 := fun a ha => by rw [← hσ a, ha, map_zero]
    have fxz : form σ W.J H.x z = 0 := by
      have e := congrFun h1 0
      rw [gram_mulVec_entry, cX0, hM, hE_eq hσ] at e
      exact σinj _ ((mul_eq_zero.1 e).resolve_left hc)
    have fyz : form σ W.J H.y z = 0 := by
      have e := congrFun h2 0
      rw [gram_mulVec_entry, cY0, ← one_smul E z, sX, Pi.zero_apply, mul_one] at e
      have hs : σ c₀⁻¹ ≠ 0 := fun h => inv_ne_zero hc (σinj _ h)
      rcases mul_eq_zero.1 e with h | h
      · rcases mul_eq_zero.1 h with h | h
        · exact absurd h hs
        · exact absurd h hc
      · exact σinj _ h
    have hdet : W₁.J.det ≠ 0 := fun h => hND₁.2 (by
      rw [hM₁, Matrix.det_smul, show (W₁.J.map σ).det = σ W₁.J.det by exact (RingHom.map_det (σ : E →+* E) W₁.J).symm, h, map_zero, mul_zero])
    obtain ⟨α, β, z₁, rfl⟩ := GlobalTheory.UnipCocptForm.decomp σ W.J W₁.J H.x H.y H.ι hskew hσ hn hxx hyy hxy horth hg hdet z
    have fzx : form σ W.J (α • H.x + β • H.y + H.ι *ᵥ z₁) H.x = -β := by
      rw [GlobalTheory.UnipCocptForm.form_add, GlobalTheory.UnipCocptForm.form_add, GlobalTheory.UnipCocptForm.form_smul,
        GlobalTheory.UnipCocptForm.form_smul, hxx, hyx, (horth z₁).1]; ring
    have fzy : form σ W.J (α • H.x + β • H.y + H.ι *ᵥ z₁) H.y = α := by
      rw [GlobalTheory.UnipCocptForm.form_add, GlobalTheory.UnipCocptForm.form_add, GlobalTheory.UnipCocptForm.form_smul,
        GlobalTheory.UnipCocptForm.form_smul, hxy, hyy, (horth z₁).2]; ring
    have hβ : β = 0 := by
      have := GlobalTheory.UnipCocptForm.form_swap σ W.J hskew hσ (α • H.x + β • H.y + H.ι *ᵥ z₁) H.x
      rw [fzx, fxz, map_zero, neg_zero] at this
      exact neg_eq_zero.1 this
    have hα : α = 0 := by
      have := GlobalTheory.UnipCocptForm.form_swap σ W.J hskew hσ (α • H.x + β • H.y + H.ι *ᵥ z₁) H.y
      rwa [fzy, fyz, map_zero, neg_zero] at this
    subst hα hβ
    simp only [zero_smul, zero_add] at h1 h2 h3 ⊢
    have k1 : (cT (σ : E →+* E) Xf * M₁) *ᵥ z₁ = 0 := funext fun i => by
      have e := congrFun h1 i.succ
      rw [gram_mulVec_entry, cXs, hι] at e
      rw [gram_mulVec_entry, e]; rfl
    have k2 : (cT (σ : E →+* E) Yf * M₁) *ᵥ z₁ = 0 := funext fun i => by
      have e := congrFun h2 i.succ
      rw [gram_mulVec_entry, cYs, hι] at e
      rw [gram_mulVec_entry, e]; rfl
    rw [hW.aniso z₁ k1 k2 ((hι z₁ z₁).symm.trans h3), Matrix.mulVec_zero]
end GlobalTheory.PlaneFrameCons
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedLatticeMapExists
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts GlobalTheory.GeoLevel
open GlobalTheory.Member (FinCong IotaOK)
open GlobalTheory.LevelCusp (IsMatch)
open GlobalTheory.Dict (castFr)
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GeoLevel.ModHalf

theorem mem_of_coprime {R A : Type} [CommRing R] [AddCommGroup A] [Module R A] {I J : Ideal R} (h : I ⊔ J = ⊤)
    (f : A →ₗ[R] A) (hf : ∀ a ∈ J • (⊤ : Submodule R A), f a ∈ I • (⊤ : Submodule R A)) (a : A) :
    f a ∈ I • (⊤ : Submodule R A) := by
  have h1 : (1 : R) ∈ I ⊔ J := by rw [h]; trivial
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 h1
  have : a = x • a + y • a := by rw [← add_smul, hxy, one_smul]
  rw [this, map_add, map_smul]
  exact add_mem (Submodule.smul_mem_smul hx trivial) (hf _ (Submodule.smul_mem_smul hy trivial))

theorem map_mem_smul_top {R A : Type} [CommRing R] [AddCommGroup A] [Module R A] {J : Ideal R}
    (f : A →ₗ[R] A) {a : A} (ha : a ∈ J • (⊤ : Submodule R A)) : f a ∈ J • (⊤ : Submodule R A) := by
  refine Submodule.smul_induction_on ha (fun r hr x _ => ?_) (fun x y hx hy => ?_)
  · rw [map_smul]; exact Submodule.smul_mem_smul hr trivial
  · rw [map_add]; exact add_mem hx hy

theorem mem_of_range {R A B : Type} [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    {I J : Ideal R} {N : ℕ} (h : I * J = Ideal.span {(N : R)}) (ι : A →ₗ[R] B) (hι : Function.Injective ι)
    {x y : A} {u : B} (hu : u ∈ LinearMap.range ι) (e : ι x - ι y = N • u) : x - y ∈ I • (⊤ : Submodule R A) := by
  obtain ⟨v, rfl⟩ := hu
  rw [← map_nsmul, ← map_sub] at e
  have e' : x - y = (N : R) • v := by rw [Nat.cast_smul_eq_nsmul]; exact hι e
  rw [e']
  refine Submodule.smul_mem_smul ?_ trivial
  have : (N : R) ∈ I * J := by
    rw [h]; exact Ideal.mem_span_singleton_self _
  exact (Ideal.mul_le_inf this).1

set_option maxHeartbeats 1600000 in

theorem mem_of_finVec {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (l : Level H) (V : HSp D)
    {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (hι : LatEmb V ι) (x y : La) (w : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) (hw : w ∈ latGHat V 1)
    (h : finVec V (ι x) - finVec V (ι y) = l.M • w) : x - y ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) La) := by
  obtain ⟨u, hu, e⟩ := GlobalTheory.MarkUniq.exists_of_finVec_eq_nsmul V 1 l.M (by have := l.three_le; omega)
    (ι x - ι y) w hw ((GlobalTheory.MarkUniq.finVec_sub V (ι x) (ι y)).trans h)
  exact mem_of_range l.prod ι hι.1 (hι.2.ge hu) e

theorem isLift_mul {D : D7} {V : HSp D} {r : ℕ} {hr : V.rank = r} {β : GL (Fin r) (EAf D)}
    {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)} {g h : Formalism.L2.DIV.G0 Pg r} {κ κ' : GA D V}
    (h1 : IsLift V hr β Pg g κ) (h2 : IsLift V hr β Pg h κ') : IsLift V hr β Pg (g * h) (κ * κ') := by
  obtain ⟨a1, b1, c1⟩ := h1
  obtain ⟨a2, b2, c2⟩ := h2
  refine ⟨mul_mem a1 a2, by rw [map_mul]; exact mul_mem b1 b2, fun w => ?_⟩
  have : (⟨finR V hr (κ * κ'), by rw [map_mul]; exact mul_mem b1 b2⟩ : Formalism.L2.DIV.St β) =
      ⟨finR V hr κ, b1⟩ * ⟨finR V hr κ', b2⟩ := Subtype.ext (map_mul _ _ _)
  rw [this, map_mul, c1, c2]; rfl

theorem flip_sub {M : Type} [AddCommGroup M] (N : ℕ) {p q w : M} (e : p - q = N • w) : q - p = N • (-w) := by
  rw [smul_neg, ← e, neg_sub]

theorem cocycle {M : Type} [AddCommGroup M] (k : M →+ M) (N : ℕ) {p q s t w₁ w₂ w₃ : M}
    (e1 : p - q = N • w₁) (e2 : k q - s = N • w₂) (e3 : k p - t = N • w₃) :
    t - s = N • (k w₁ + w₂ - w₃) := by
  rw [smul_sub, smul_add, ← map_nsmul, ← e1, ← e2, ← e3, map_sub]; abel

set_option maxHeartbeats 1600000 in

theorem action_mod_half : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (l : Level H) (V : HSp D) (r : ℕ) (hr : V.rank = r) (β : GL (Fin r) (EAf D)) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)), IsLatBasis V hr β → (∀ w, w ∈ Pg ↔ l.Mb ≤ w.asIdeal) → ∀ (Dw : Datum H) (ι₀ : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)), LatEmb V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀) → ∀ γ : Formalism.L2.DIV.G0 Pg r → Dw.La →ₗ[𝓞 D.host.E] Dw.La, (∀ g, Induces Dw l V hr ι₀ β Pg g (γ g)) → (∀ a, γ 1 a - a ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) ∧ ∀ g h a, γ (g * h) a - γ g (γ h a) ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La) := by
  intro D H l V r hr β Pg hβ hPg Dw ι₀ hι γ hγ
  refine ⟨fun a => ?_, fun g h a => ?_⟩
  · refine mem_of_coprime l.coprime (γ 1 - LinearMap.id) (fun a ha => ?_) a
    obtain ⟨w, hw, e⟩ := hγ 1 1 (isLift_one V hr β Pg) a ha
    rw [map_one, Units.val_one, Matrix.one_mulVec] at e
    exact mem_of_finVec l V _ hι (γ 1 a) a (-w) (neg_mem hw) (flip_sub l.M e)
  · refine mem_of_coprime l.coprime (γ (g * h) - γ g ∘ₗ γ h) (fun a ha => ?_) a
    obtain ⟨κ, hκ⟩ := GlobalTheory.T.level_group_lift_exists D H l V r hr β Pg hβ hPg g
    obtain ⟨κ', hκ'⟩ := GlobalTheory.T.level_group_lift_exists D H l V r hr β Pg hβ hPg h
    obtain ⟨w₁, hw₁, e₁⟩ := hγ h κ' hκ' a ha
    obtain ⟨w₂, hw₂, e₂⟩ := hγ g κ hκ (γ h a) (map_mem_smul_top (γ h) ha)
    obtain ⟨w₃, hw₃, e₃⟩ := hγ (g * h) (κ * κ') (isLift_mul hκ hκ') a ha
    rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec] at e₃
    have hk := (GlobalTheory.Member.AALev.congruences_agree D V κ).1.2
      ((GlobalTheory.T.level_lift_finite_congruence D H l V r hr β Pg hβ hPg).1 g κ hκ) w₁ hw₁
    exact mem_of_finVec l V _ hι (γ (g * h) a) (γ g (γ h a)) _ (sub_mem (add_mem hk hw₂) hw₃)
      (cocycle (Matrix.mulVecLin (finHom V κ).1).toAddMonoidHom l.M e₁ e₂ e₃)

end GlobalTheory.GeoLevel.ModHalf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntValuationPrimeBack
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal
open IsDedekindDomain

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GalSup

section Prime

variable {K : Type} [Field K] [NumberField K]

abbrev primeBack (s : K ≃+* K) (la : HeightOneSpectrum (𝓞 K)) : HeightOneSpectrum (𝓞 K) :=
  HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s).symm la

theorem count_equiv {R S : Type} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [DecidableEq (Associates (Ideal R))] [∀ p : Associates (Ideal R), Decidable (Irreducible p)]
    [DecidableEq (Associates (Ideal S))] [∀ p : Associates (Ideal S), Decidable (Irreducible p)]
    (e : R ≃+* S) (p : HeightOneSpectrum R) {I : Ideal R} (hI : I ≠ ⊥) :
    (Associates.mk (HeightOneSpectrum.equivOfRingEquiv e p).asIdeal).count (Associates.mk (I.comap e.symm)).factors =
      (Associates.mk p.asIdeal).count (Associates.mk I).factors := by
  have hI' : I.comap e.symm ≠ ⊥ := by
    rw [← Ideal.map_comap_of_equiv]
    exact fun h => hI ((Ideal.map_eq_bot_iff_of_injective e.injective).1 h)
  refine eq_of_forall_le_iff fun k => ?_
  rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.2 hI') (HeightOneSpectrum.associates_irreducible _),
    ← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.2 hI) (HeightOneSpectrum.associates_irreducible _),
    ← Associates.mk_pow, ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd, Associates.mk_le_mk_iff_dvd,
    Ideal.dvd_iff_le, Ideal.dvd_iff_le]
  have : (HeightOneSpectrum.equivOfRingEquiv e p).asIdeal = p.asIdeal.map (e : R →+* S) := by
    rw [Ideal.map_comap_of_equiv]; rfl
  rw [this, ← Ideal.map_pow, Ideal.map_comap_of_equiv]
  exact Ideal.comap_le_comap_iff_of_surjective e.symm e.symm.surjective _ _

theorem intValuation_primeBack (s : K ≃+* K) (la : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) :
    (primeBack s la).intValuation a = la.intValuation (RingOfIntegers.mapRingEquiv s a) := by
  classical
  by_cases ha : a = 0
  · subst ha; simp
  have ha' : RingOfIntegers.mapRingEquiv s a ≠ 0 := by simpa using ha
  rw [HeightOneSpectrum.intValuation_if_neg _ ha, HeightOneSpectrum.intValuation_if_neg _ ha']
  have hc : (Ideal.span {RingOfIntegers.mapRingEquiv s a}).comap (RingOfIntegers.mapRingEquiv s).symm.symm =
      Ideal.span {a} := by
    rw [← Ideal.map_comap_of_equiv, Ideal.map_span, Set.image_singleton]
    simp
  have := count_equiv (RingOfIntegers.mapRingEquiv s).symm la
    (I := Ideal.span {RingOfIntegers.mapRingEquiv s a}) (by simpa using ha')
  rw [hc] at this
  rw [this]

theorem valuation_primeBack (s : K ≃+* K) (la : HeightOneSpectrum (𝓞 K)) (x : K) :
    (primeBack s la).valuation K x = la.valuation K (s x) := by
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have hs : ∀ z : 𝓞 K, s (algebraMap (𝓞 K) K z) = algebraMap (𝓞 K) K (RingOfIntegers.mapRingEquiv s z) :=
    fun _ => rfl
  rw [map_div₀, map_div₀, map_div₀, hs, hs, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, intValuation_primeBack, intValuation_primeBack]

theorem vLa_primeBack (s : K ≃+* K) (la : HeightOneSpectrum (𝓞 K)) (x : K) :
    vLa (primeBack s la) x = vLa la (s x) := by
  simp only [vLa, valuation_primeBack]

end Prime
end GlobalTheory.GalSup

namespace GlobalTheory.GalSup

section Pts

open ReciprocityTheory.ChartRestriction.G

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F)

def changeEmbedding {L : Type} [CommRing L] (ι₀ ι₁ : c'.F →+* L) (κ : c.F →+* L)
    (h₀ : ∀ a, ι₀ (incF c c' hle a) = κ a) (h₁ : ∀ a, ι₁ (incF c c' hle a) = κ a)
    (y : letI := ι₀.toAlgebra; FrPt Xo c' L) : letI := ι₁.toAlgebra; FrPt Xo c' L :=
  letI : Algebra c.F L := κ.toAlgebra
  let y₀ : FrPt Xo c L := (letI : Algebra c'.F L := ι₀.toAlgebra; y.res hle h₀)
  letI : Algebra c'.F L := ι₁.toAlgebra
  y₀.ext hle h₁

theorem evR_rulBC {L : Type} [CommRing L] (ι₀ : c'.F →+* L) (κ : c.F →+* L)
    (h₀ : ∀ a, ι₀ (incF c c' hle a) = κ a) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a n)
    (y : letI := ι₀.toAlgebra; FrPt Xo c' L) :
    (letI := ι₀.toAlgebra; evR Xo c' (rulBC hle f) y) =
      (letI : Algebra c.F L := κ.toAlgebra; letI := ι₀.toAlgebra; evR Xo c f (y.res hle h₀)) := by
  letI : Algebra c.F L := κ.toAlgebra
  letI := ι₀.toAlgebra
  exact ((rulBC_sec_val_linear E H Dw l Xo c c' hle).1 a n f hf).2 L h₀ y

theorem integral_reread {T : CDVR} (ι₀ ι₁ : c'.F →+* T.Fr) (κ : c.F →+* T.Fr)
    (h₀ : ∀ a, ι₀ (incF c c' hle a) = κ a) (h₁ : ∀ a, ι₁ (incF c c' hle a) = κ a)
    (y : letI := ι₀.toAlgebra; FrPt Xo c' T.Fr) (hy : Integral T ι₀ y) :
    Integral T ι₁ (changeEmbedding hle ι₀ ι₁ κ h₀ h₁ y) := by
  have key : ∀ (τ : E →+* ℂ) (b : 𝓞 E), ι₁ (embK c' τ b) = ι₀ (embK c' τ b) := fun τ b => by
    rw [← embK_incF hle τ b, h₀, h₁]
  have eig : ∀ (G : SAB H (Sp T.V)) τ (w : epsOver T.V T.V ⟶ G.G),
      IsEigV c' ι₁ G τ w ↔ IsEigV c' ι₀ G τ w := fun G τ w => by
    unfold IsEigV
    simp only [key]
  obtain ⟨G, t', m1, m2, ⟨ub, h1, h2, h3, h4⟩, rest⟩ := hy
  exact ⟨G, t', m1, m2, ⟨ub, h1, fun τ i => (eig G τ _).2 (h2 τ i),
    fun τ w ht he => h3 τ w ht ((eig G τ w).1 he), h4⟩, rest⟩

end Pts
end GlobalTheory.GalSup

namespace GlobalTheory.GalSup

open ReciprocityTheory.ChartRestriction.G

theorem evI_sum {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr} (y : IntFr Xo c T io) {m : ℕ}
    (b : Fin m → c.F) (g : Fin m → Rul Xo c) :
    evI y (∑ i, b i • g i) = ∑ i, io (b i) * evI y (g i) := by
  have h := map_sum (AddMonoidHom.mk' (evI y) (evI_add y)) (fun i => b i • g i) Finset.univ
  simp only [AddMonoidHom.mk'_apply] at h
  rw [h]
  simp only [evI_smul]

theorem intAt_galois : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (s : c'.F ≃+* c'.F), (∀ x : c.F, s (incF c c' hle x) = incF c c' hle x) → ∀ (m : ℕ) (as : Fin m → c'.F) (fs : Fin m → Rul Xo c), (∀ i, fs i ∈ sec Xo c a n) → IntAt Xo c' (∑ i, as i • rulBC hle (fs i)) → IntAt Xo c' (∑ i, s (as i) • rulBC hle (fs i)) := by
  intro E _ _ _ H Dw l Xo c c' hle a n s hs m as fs hfs hint la v hv
  obtain ⟨⟨q, T, ι, e, ho, y, hy, eta, heta, hq⟩, rfl⟩ := hv
  subst hq
  show 0 ≤ nval T.V e (evI y _)
  let κ : c.F →+* T.Fr := ι.comp (incF c c' hle)
  let ι₁ : c'.F →+* T.Fr := ι.comp (s : c'.F →+* c'.F)
  have h₀ : ∀ x, ι (incF c c' hle x) = κ x := fun _ => rfl
  have h₁ : ∀ x, ι₁ (incF c c' hle x) = κ x := fun x => by
    show ι (s (incF c c' hle x)) = ι (incF c c' hle x)
    rw [hs x]
  let y₁ : IntFr Xo c' T ι₁ := ⟨changeEmbedding hle ι ι₁ κ h₀ h₁ y.1,
    (letI := ι₁.toAlgebra; GlobalTheory.FlagTan.fromTest_of_isLocalRing _), integral_reread hle ι ι₁ κ h₀ h₁ y.1 y.2.2⟩
  have ho₁ : OverLa (primeBack s la) T.V ι₁ e := ⟨ho.1, fun x => by
    rw [vLa_primeBack]; exact ho.2 (s x)⟩
  have key : 0 ≤ nval T.V e (evI y₁ (∑ i, as i • rulBC hle (fs i))) :=
    hint (primeBack s la) _ ⟨PtV.mk (primeBack s la) ho₁ y₁ hy () trivial, rfl⟩
  have e1 : evI y (∑ i, s (as i) • rulBC hle (fs i)) = evI y₁ (∑ i, as i • rulBC hle (fs i)) := by
    rw [evI_sum, evI_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    unfold evI
    rw [evR_rulBC hle ι κ h₀ (hfs i), evR_rulBC hle ι₁ κ h₁ (hfs i)]
    rfl
  rw [e1]
  exact key

end GlobalTheory.GalSup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantMeasureChartBallOrthonormalLowerBoundStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantMeasure_chartBall_orthonormal_lower_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ENNReal.ofReal (Real.exp (-(C * ((X.Ψ.card : ℝ) * r) ^ 8))) ≤ ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x (Metric.ball (0 : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (1 / (100 * (r : ℝ) ^ 2)) ∩ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x) := by
  first | exact @GlobalTheory.BallVol.ballvol | exact GlobalTheory.BallVol.ballvol | (intros; apply GlobalTheory.BallVol.ballvol <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleCharacterGoodIdempotentCuspidalProducStatement
section
open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES Formalism.BasicNotions Formalism.L2.DIV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_character_good_idempotent_cuspidal_product' : ∀ (D : D7) [Fintype (G0g D.nd)], (∀ k : Fin 2, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; ∃ (C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod (D.host.g k))) (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod (D.host.g k)) C), ∀ f, D.ntypes.eSer k f = Formalism.L2.NT.eSerO O D.R.r f) → ∀ χ : G0g D.nd → ℂ, Formalism.L2.NT.IsIrrChar χ → ∑ g, D.ntypes.e0.coeff g * χ g = χ 1 → ∃ θ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), GL (Fin D.R.r) (ZMod (D.host.g kv.1)) → ℂ, (∀ kv : (Σ k : Fin 2, D.nd.PlG k), haveI : Fact (D.host.g kv.1).Prime := ⟨D.host.g_prime kv.1⟩; GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsCuspProdChar (θ kv)) ∧ ∀ g, χ g = ∏ kv : (Σ k : Fin 2, D.nd.PlG k), θ kv (g kv) := by
  first | exact @GlobalTheory.GoodFactor.irreducible_character_good_idempotent_cuspidal_product | exact GlobalTheory.GoodFactor.irreducible_character_good_idempotent_cuspidal_product | (intros; apply GlobalTheory.GoodFactor.irreducible_character_good_idempotent_cuspidal_product <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenOfSpecializesIff
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel GlobalTheory.UPelLevel
open scoped CategoryTheory.Obj TensorProduct

set_option autoImplicit false

noncomputable section

open Set Topology

namespace GlobalTheory.SpecGenClopen

theorem isClosed_of_stable (X : Scheme.{0}) [IsLocallyNoetherian X] (T : Set X)
    (hs : StableUnderSpecialization T) (hg : StableUnderGeneralization T) : IsClosed T := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x) trivial
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  haveI : TopologicalSpace.NoetherianSpace (U : Set X) := noetherianSpace_of_isAffineOpen U hU
  let T' : Set (U : Set X) := Subtype.val ⁻¹' T
  have key : ∀ Z : Set (U : Set X), IsIrreducible Z → (Z ∩ T').Nonempty → Z ⊆ T' := by
    rintro Z hZ ⟨t, htZ, htT⟩ z hz
    have hI : IsIrreducible (closure (Subtype.val '' Z : Set X)) :=
      (hZ.image _ continuous_subtype_val.continuousOn).closure
    obtain ⟨g₀, hg₀⟩ := QuasiSober.sober hI isClosed_closure
    have h1 : g₀ ⤳ (t : X) := hg₀.specializes (subset_closure ⟨t, htZ, rfl⟩)
    have h2 : g₀ ⤳ (z : X) := hg₀.specializes (subset_closure ⟨z, hz, rfl⟩)
    exact hs h2 (hg h1 htT)
  have hT' : T' = ⋃ Z ∈ {Z ∈ irreducibleComponents (U : Set X) | (Z ∩ T').Nonempty}, Z := by
    ext t
    refine ⟨fun ht => Set.mem_biUnion ⟨irreducibleComponent_mem_irreducibleComponents t,
      ⟨t, mem_irreducibleComponent, ht⟩⟩ mem_irreducibleComponent, fun ht => ?_⟩
    obtain ⟨Z, ⟨hZ, hZT⟩, htZ⟩ := Set.mem_iUnion₂.1 ht
    exact key Z hZ.1 hZT htZ
  have hc : IsClosed T' := by
    rw [hT']
    exact (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset fun _ h => h.1).isClosed_biUnion
      fun Z h => isClosed_of_mem_irreducibleComponents Z h.1
  refine ⟨Subtype.val '' T'ᶜ, ?_, U.isOpen.isOpenEmbedding_subtypeVal.isOpenMap _ hc.isOpen_compl, ⟨x, hxU⟩, hx, rfl⟩
  rintro _ ⟨t, ht, rfl⟩
  exact ht

theorem isClopen_of_specializes_iff : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (Z : Set X),
    (∀ x y : X, x ⤳ y → (x ∈ Z ↔ y ∈ Z)) → IsClopen Z := by
  intro X _ Z h
  have hs : StableUnderSpecialization Z := fun x y hxy hx => (h x y hxy).1 hx
  have hg : StableUnderGeneralization Z := fun x y hxy hx => (h y x hxy).2 hx
  exact ⟨isClosed_of_stable X Z hs hg, isClosed_compl_iff.1 (isClosed_of_stable X Zᶜ
    (stableUnderSpecialization_compl_iff.2 hg) (stableUnderGeneralization_compl_iff.2 hs))⟩

end GlobalTheory.SpecGenClopen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFundamentalDomainSaturatedFundamentalSetFramesStatement
section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume GlobalTheory.FlagQuotHaar
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFundamentalDomain_saturated_fundamentalSet_frames : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {c : ℝ≥0∞}, HaarChart X c → ∀ {x0 : Frame X.Ψ r}, IsOrth X x0 → ∀ {FF : Set (V (nd X))}, IsFundSet X x0 FF → ∀ (Λ : Subgroup (RealGrp X)), (∀ s, s ∈ Λ ↔ ∃ γ ∈ X.Γ, lact γ (baseFr X) = frameOf X s) → IsFundamentalDomain Λ (frameOf X ⁻¹' GlobalTheory.Unfold.satFrames X x0 FF) (haarR X) := by
  first | exact @GlobalTheory.FundFrames.isFundamentalDomain_satFrames | exact GlobalTheory.FundFrames.isFundamentalDomain_satFrames | (intros; apply GlobalTheory.FundFrames.isFundamentalDomain_satFrames <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackDescentAlongGaloisCoverStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGrpPullback_descent_along_galoisCover : ∀ (S S₁ Y : Scheme.{0}) (π₁ : S₁ ⟶ S) (Ga : Type) [Group Ga] (ρ₁ : Ga → (S₁ ⟶ S₁)) (f : S ⟶ Y) (A' : Over S₁) (A : Over S) (B : Over Y) [GrpObj A'] [GrpObj A] [GrpObj B] (φ₁ : A'.left ⟶ A.left) (ψ : A'.left ⟶ B.left) (φ : A.left ⟶ B.left), GlobalTheory.ZM.IsGaloisCover Ga ρ₁ π₁ → IsGrpPullback A' A π₁ φ₁ → IsGrpPullback A' B (π₁ ≫ f) ψ → φ₁ ≫ φ = ψ → IsGrpPullback A B f φ := by
  first | exact @GlobalTheory.GaloisCartDesc.isGrpPullback_of_galoisCover | exact GlobalTheory.GaloisCartDesc.isGrpPullback_of_galoisCover | (intros; apply GlobalTheory.GaloisCartDesc.isGrpPullback_of_galoisCover <;> assumption)
end


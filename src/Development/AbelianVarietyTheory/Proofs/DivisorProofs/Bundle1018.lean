import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0039
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0024
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnFrameA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0978
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0983
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0045

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AevalEqZeroOfSqEqZeroOfPosDefSimilitude
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder

namespace GlobalTheory.SimNormSq

open Polynomial

theorem commute_aeval_of_commute {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    {x y : A} (h : Commute y x) (p : R[X]) : Commute y (aeval x p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact hp.add_right hq
  | monomial n a =>
    rw [aeval_monomial]; exact (Algebra.commute_algebraMap_right a y).mul_right (h.pow_right n)

theorem eq_zero_of_conjTranspose_mul_mul_eq_zero {n : ℕ} {H A : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.PosDef) (h : Aᴴ * H * A = 0) : A = 0 := by
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [Matrix.zero_mulVec]
  by_contra hne
  have hpos := hH.dotProduct_mulVec_pos hne
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, h,
    Matrix.zero_mulVec, dotProduct_zero] at hpos
  exact lt_irrefl _ hpos

end GlobalTheory.SimNormSq

namespace GlobalTheory

open Polynomial

theorem aeval_eq_zero_of_mul_self_eq_zero_of_similitude :
    ∀ (n : ℕ) (H M : Matrix (Fin n) (Fin n) ℂ) (s : ℝ), H.PosDef → 0 < s →
      Mᴴ * H * M = (s : ℂ) • H → ∀ P : Polynomial ℂ,
        Polynomial.aeval M P * Polynomial.aeval M P = 0 → Polynomial.aeval M P = 0 := by
  intro n H M s hH hs hM P hP
  have hdet : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit
  have hHinv : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul H hdet
  have hHinv' : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv H hdet
  have hHh : Hᴴ = H := hH.1
  have hHih : (H⁻¹)ᴴ = H⁻¹ := by rw [conjTranspose_nonsing_inv, hHh]
  have hc : ∀ A : Matrix (Fin n) (Fin n) ℂ, H⁻¹ * (H * A) = A := fun A => by
    rw [← Matrix.mul_assoc, hHinv, Matrix.one_mul]
  have hc' : ∀ A : Matrix (Fin n) (Fin n) ℂ, H * (H⁻¹ * A) = A := fun A => by
    rw [← Matrix.mul_assoc, hHinv', Matrix.one_mul]
  have hM' : Mᴴ * (H * M) = (s : ℂ) • H := by rw [← Matrix.mul_assoc]; exact hM
  set D := H⁻¹ * Mᴴ * H with hD
  have hDM : D * M = (s : ℂ) • 1 := by
    rw [hD]; simp only [Matrix.mul_assoc]; rw [hM', Matrix.mul_smul, hHinv]
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hMD : M * D = (s : ℂ) • 1 := by
    have h1 : ((s : ℂ)⁻¹ • D) * M = 1 := by
      rw [Matrix.smul_mul, hDM, smul_smul, inv_mul_cancel₀ hs0, one_smul]
    have h2 := mul_eq_one_comm.mp h1
    rw [Matrix.mul_smul] at h2
    calc M * D = (s : ℂ) • ((s : ℂ)⁻¹ • (M * D)) := by
          rw [smul_smul, mul_inv_cancel₀ hs0, one_smul]
      _ = (s : ℂ) • 1 := by rw [h2]
  have hcomm : Commute D M := by
    show D * M = M * D
    rw [hDM, hMD]
  have hall : ∀ Y, Commute Y M → Commute Y (aeval M P) := fun Y hY =>
    SimNormSq.commute_aeval_of_commute hY P
  have hDW := hall D hcomm
  generalize hW : aeval M P = W at hP hDW ⊢
  have key : Commute (H⁻¹ * Wᴴ * H) M := by
    have h1 : Wᴴ * (H * (M * H⁻¹)) = H * (M * (H⁻¹ * Wᴴ)) := by
      have h0 := congrArg conjTranspose hDW.eq
      simp only [hD, conjTranspose_mul, conjTranspose_conjTranspose, hHh, hHih,
        Matrix.mul_assoc] at h0
      exact h0
    show H⁻¹ * Wᴴ * H * M = M * (H⁻¹ * Wᴴ * H)
    calc H⁻¹ * Wᴴ * H * M = H⁻¹ * (Wᴴ * (H * (M * H⁻¹))) * H := by
          simp only [Matrix.mul_assoc, hHinv, Matrix.mul_one]
      _ = H⁻¹ * (H * (M * (H⁻¹ * Wᴴ))) * H := by rw [h1]
      _ = M * (H⁻¹ * Wᴴ * H) := by
          simp only [Matrix.mul_assoc, hc]
  have hXW : Commute (H⁻¹ * Wᴴ * H) W := by
    have h4 := hall _ key
    rwa [hW] at h4
  have hX : (H⁻¹ * Wᴴ * H * W)ᴴ * H * (H⁻¹ * Wᴴ * H * W) = 0 := by
    calc (H⁻¹ * Wᴴ * H * W)ᴴ * H * (H⁻¹ * Wᴴ * H * W)
        = Wᴴ * H * (W * (H⁻¹ * Wᴴ * H)) * W := by
          simp only [conjTranspose_mul, conjTranspose_conjTranspose, hHh, hHih,
            Matrix.mul_assoc, hc]
      _ = Wᴴ * H * ((H⁻¹ * Wᴴ * H) * W) * W := by rw [← hXW.eq]
      _ = 0 := by simp only [Matrix.mul_assoc, hP, Matrix.mul_zero]
  have hX0 := SimNormSq.eq_zero_of_conjTranspose_mul_mul_eq_zero hH hX
  have hW2 : Wᴴ * H * W = 0 := by
    have h3 : H * (H⁻¹ * Wᴴ * H * W) = Wᴴ * H * W := by simp only [Matrix.mul_assoc, hc']
    rw [← h3, hX0, Matrix.mul_zero]
  exact SimNormSq.eq_zero_of_conjTranspose_mul_mul_eq_zero hH hW2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapInjective
section
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.CentTorus
open scoped TensorProduct Classical

namespace GlobalTheory.CentAtP

variable {p : ℕ} [Fact p.Prime]

def conjF (G : HTGroup p) : G.F →ₐ[ℚ] G.F :=
  ((IsCMField.complexConj G.F : G.F →+* G.F)).toRatAlgHom

def rhoL (G : HTGroup p) (P : Pair G) (w : Fin G.m) :
    ℚ_[p] ⊗[ℚ] algF P →ₐ[ℚ_[p]] Matrix (Fin G.n) (Fin G.n) (G.Fw w) :=
  (G.locW w).comp (Algebra.TensorProduct.map (AlgHom.id ℚ_[p] ℚ_[p])
    ((algF P).val : algF P →+* G.C).toRatAlgHom)

def inclF (G : HTGroup p) (P : Pair G) : ℚ_[p] ⊗[ℚ] G.F →ₐ[ℚ_[p]] ℚ_[p] ⊗[ℚ] algF P :=
  Algebra.TensorProduct.map (AlgHom.id ℚ_[p] ℚ_[p]) (algebraMap G.F (algF P)).toRatAlgHom

variable {G : HTGroup p} {P : Pair G}

theorem rhoL_tmul (w : Fin G.m) (a : ℚ_[p]) (x : algF P) :
    rhoL G P w (a ⊗ₜ x) = algebraMap ℚ_[p] _ a * G.rho w (x : G.C) := by
  simp [rhoL, HTGroup.locW, Algebra.TensorProduct.lift_tmul]
  rfl

theorem rhoL_one_tmul (w : Fin G.m) (x : algF P) :
    rhoL G P w ((1 : ℚ_[p]) ⊗ₜ x) = G.rho w (x : G.C) := by
  rw [rhoL_tmul, map_one, one_mul]

theorem algebraMap_injective (G : HTGroup p) (P : Pair G) :
    Function.Injective (algebraMap ℚ_[p] (ℚ_[p] ⊗[ℚ] algF P)) := by
  intro a b h
  have hL : Function.Injective (algebraMap ℚ (algF P)) := (algebraMap ℚ (algF P)).injective
  apply Algebra.TensorProduct.includeLeft_injective (R := ℚ) (S := ℚ_[p]) (A := ℚ_[p]) (B := algF P) hL
  simpa [Algebra.TensorProduct.algebraMap_apply] using h

theorem mem_simT_iff {k : Type} [Field k] {A : Type} [CommRing A] [Algebra k A] {c : A →ₐ[k] A} {x : Aˣ} :
    x ∈ GlobalTheory.LKTorus.simT k c ↔ ∃ t : kˣ, (x : A) * c x = algebraMap k A t := Iff.rfl

section Phi

variable (G P) (c : algF P →ₐ[ℚ] algF P)

def nuP : GlobalTheory.LKTorus.simT ℚ_[p] (extC ℚ_[p] c) →* ℚ_[p]ˣ where
  toFun s := Classical.choose (mem_simT_iff.1 s.2)
  map_one' := by
    apply Units.ext
    apply algebraMap_injective G P
    rw [← Classical.choose_spec (mem_simT_iff.1 (1 : GlobalTheory.LKTorus.simT ℚ_[p] (extC ℚ_[p] c)).2)]
    simp [Algebra.TensorProduct.one_def]
  map_mul' s t := by
    apply Units.ext
    apply algebraMap_injective G P
    rw [← Classical.choose_spec (mem_simT_iff.1 (s * t).2), Units.val_mul, map_mul,
      ← Classical.choose_spec (mem_simT_iff.1 s.2), ← Classical.choose_spec (mem_simT_iff.1 t.2)]
    simp only [Subgroup.coe_mul, Units.val_mul, map_mul]
    ring

variable {G P c}

def gamL (P : Pair G) : algF P := ⟨(P.γ : G.C), Algebra.subset_adjoin rfl⟩

theorem rhoL_comm (w : Fin G.m) (y : ℚ_[p] ⊗[ℚ] algF P) :
    G.rho w (P.γ : G.C) * rhoL G P w y = rhoL G P w y * G.rho w (P.γ : G.C) := by
  have h : G.rho w (P.γ : G.C) = rhoL G P w ((1 : ℚ_[p]) ⊗ₜ gamL P) := (rhoL_one_tmul w (gamL P)).symm
  rw [h, ← map_mul, ← map_mul, mul_comm]

variable (G P c)

def phiG : GlobalTheory.LKTorus.simT ℚ_[p] (extC ℚ_[p] c) →* Gp G :=
  (nuP G P c).prod (MonoidHom.pi fun w =>
    (Units.map ((rhoL G P w).toRingHom.toMonoidHom)).comp (GlobalTheory.LKTorus.simT ℚ_[p] (extC ℚ_[p] c)).subtype)

theorem phiG_mem (s : GlobalTheory.LKTorus.simT ℚ_[p] (extC ℚ_[p] c)) :
    phiG G P c s ∈ Subgroup.centralizer {P.atP} := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  refine Prod.ext (mul_comm _ _) (funext fun w => Units.ext ?_)
  exact (rhoL_comm w _).symm

def phiP : GlobalTheory.LKTorus.simT ℚ_[p] (extC ℚ_[p] c) →* Subgroup.centralizer {P.atP} :=
  (phiG G P c).codRestrict _ (phiG_mem G P c)

end Phi

end GlobalTheory.CentAtP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticFibreDescriptionUnique
section
namespace GlobalTheory.AnUniq

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem exp_eq {S : Scheme.{0}} {G : Over S} [GrpObj G] {y : Sp ℂ ⟶ S} {g : ℕ}
    {e e' : (Fin g → ℂ) → (Over.mk y ⟶ G)} (he : ∀ z w, e (z + w) = e z * e w)
    (he' : ∀ z w, e' (z + w) = e' z * e' w)
    (hol : IsHolTo Set.univ (fun z => (e z).left)) (hol' : IsHolTo Set.univ (fun z => (e' z).left))
    (u : Fin g → (Sp (DualNumber ℂ) ⟶ G.left)) (hd : ∀ i, IsDerivAt0 (fun z => (e z).left) (Pi.single i 1) (u i))
    (hd' : ∀ i, IsDerivAt0 (fun z => (e' z).left) (Pi.single i 1) (u i)) : e = e' := by
  have h0 : e 0 = e' 0 := (HolHom.map_zero_eq_one he).trans (HolHom.map_zero_eq_one he').symm
  refine HolHom.eq_of_fderiv_eq he he' hol hol' fun U hU f =>
    ContinuousLinearMap.coe_injective ((Pi.basisFun ℂ _).ext fun i => ?_)
  rw [Pi.basisFun_apply]
  exact (((HolHom.isDerivAt0_iff _ _ _).1 (hd i)).2 U hU f).symm.trans
    (((HolHom.isDerivAt0_iff _ _ _).1 (hd' i)).2 U (h0 ▸ hU :) f)

theorem fr_eq {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ}
    (Φ Φ' : AnFr A L x0 g) (he : ∀ z, Φ'.e z = Φ.e z) (hH : ∀ z w, hermForm Φ'.Hm z w = hermForm Φ.Hm z w)
    (j : L.L.ι) (z : Fin g → ℂ) (hj : ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j) : Φ.fr j z = Φ'.fr j z := by
  choose c hc using Φ.exists_chart_e
  have ne' : ∀ j z, ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j → Φ'.fr j z ≠ 0 := fun j z h => Φ'.fr_ne j z (by rw [he]; exact h)
  let q : (Fin g → ℂ) → ℂ := fun z => Φ.fr (c z) z / Φ'.fr (c z) z
  have key : ∀ j z, ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j → q z = Φ.fr j z / Φ'.fr j z := fun j z h => by
    have hz : ⊤ ≤ (Φ.e z).left ⁻¹ᵁ (L.L.U j ⊓ L.L.U (c z)) := fun p hp => ⟨h hp, hc z hp⟩
    have h1 := Φ.fr_g j (c z) z hz
    have h2 := Φ'.fr_g j (c z) z (by rw [he]; exact hz)
    rw [he] at h2
    rw [h1, h2, mul_div_mul_left _ _ (left_ne_zero_of_mul (h1 ▸ Φ.fr_ne j z h))]
  have hq : Differentiable ℂ q := fun z0 => by
    have hO : IsOpen {z | ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U (c z0)} := (Φ.hol (L.L.U (c z0)) 0).1
    have h' : DifferentiableOn ℂ (Φ'.fr (c z0)) {z | ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U (c z0)} := by
      simpa only [he] using Φ'.fr_hol (c z0)
    have hd : DifferentiableOn ℂ q {z | ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U (c z0)} :=
      ((Φ.fr_hol (c z0)).mul (h'.inv fun z hz => ne' _ z hz)).congr fun z hz =>
        (key _ z hz).trans (div_eq_mul_inv _ _)
    exact hd.differentiableAt (hO.mem_nhds (hc z0))
  have hper : ∀ z (a : Φ.lat), ‖q (z + Φ.lat.subtype a)‖ = ‖q z‖ := fun z a => by
    have ha' : (a : Fin g → ℂ) ∈ Φ'.lat := (Φ'.e_ker _).1 ((he _).trans ((Φ.e_ker _).2 a.2))
    have h : ⊤ ≤ (Φ.e (z + a)).left ⁻¹ᵁ L.L.U (c z) := by rw [Φ.e_add_lat a.2]; exact hc z
    have h1 := Φ.fr_per a a.2 (c z) z (hc z)
    have h2 := Φ'.fr_per a ha' (c z) z (by rw [he]; exact hc z)
    rw [hH, hH] at h2
    change ‖q (z + a)‖ = _
    rw [key _ _ h, key _ _ (hc z), h1, h2, norm_div, norm_div, norm_mul, norm_mul, norm_mul, norm_mul,
      Φ.χ_norm _ a.2, Φ'.χ_norm _ ha',
      mul_div_mul_left _ _ (mul_ne_zero one_ne_zero (norm_ne_zero_iff.2 (Complex.exp_ne_zero _)))]
  have hc0 := norm_periodic_const_range Φ.lat.subtype
    (by rw [AddSubgroup.coe_subtype, Subtype.range_coe]; exact Φ.span) q hq hper z 0
  have h0 : q 0 = 1 := by
    have := Φ'.fr_0 (c 0) (by rw [he]; exact hc 0)
    rw [← Φ.fr_0 (c 0) (hc 0)] at this
    change Φ.fr (c 0) 0 / Φ'.fr (c 0) 0 = 1
    rw [this, div_self (Φ.fr_ne _ _ (hc 0))]
  rw [h0, key j z hj] at hc0
  exact (div_eq_one_iff_eq (ne' j z hj)).1 hc0

end GlobalTheory.AnUniq

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.AnUniq.anFib_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A A' : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → A.ex = A'.ex ∧ ∀ ϑ, A.Reads 1 y.s ϑ ↔ A'.Reads 1 y.s ϑ := by
  intro E _ _ _ H Dw l Xo c _ r g X bas idx e x L y A A' hs hx hL
  have hex : A.ex = A'.ex := AnUniq.exp_eq A.ex_add A'.ex_add A.hol A'.hol (fun i => y.u (e i).1 (e i).2)
    (fun i => by simpa only [Equiv.symm_apply_apply] using A.der (e i))
    (fun i => by simpa only [Equiv.symm_apply_apply] using A'.der (e i))
  obtain ⟨Φ, k₁, f₁, -, m₁, -⟩ := AnFib.exists_anPt E H Dw l Xo c r g X bas idx e x L y A hs hx hL
  obtain ⟨Φ', k₂, f₂, -, m₂, -⟩ := AnFib.exists_anPt E H Dw l Xo c r g X bas idx e x L y A' hs hx hL
  have hfr := AnUniq.fr_eq Φ.toAnFr Φ'.toAnFr (fun z => by rw [k₁, k₂, hex]) (fun z w => by rw [m₁, m₂])
  simp only [k₁, f₁, f₂] at hfr
  refine ⟨hex, fun ϑ => ⟨fun h j z pt h1 h2 hj => ?_, fun h j z pt h1 h2 hj => ?_⟩⟩
  · rw [← hex] at h1 hj
    rw [← hfr j z hj]
    exact h j z pt h1 h2 hj
  · rw [hfr j z hj]
    rw [hex] at h1 hj
    exact h j z pt h1 h2 hj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseDictionaryExistsGoodEmbedding
section
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead

variable {D : D7}

theorem archM_mul' (V : HSp D) (th : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (g g' : GA D V) :
    archM V th (g * g') = archM V th g * archM V th g' := by
  simp only [archM, map_mul, Units.val_mul, Matrix.map_mul]

theorem archM_one' (V : HSp D) (th : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) :
    archM V th 1 = 1 := by
  simp only [archM, map_one, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem archM_det_unit (V : HSp D) (th : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (g : GA D V) :
    IsUnit (archM V th g).det :=
  Matrix.isUnit_det_of_right_inverse (B := archM V th g⁻¹) (by rw [← archM_mul', mul_inv_cancel, archM_one'])

theorem archM_rational (V : HSp D) (δ : GA D V) (hδ : δ ∈ GQ V) :
    ∃ δ₀ : GL (Fin V.rank) D.host.E,
      ∀ (τ : D.host.E →+* ℂ) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ), IsInfEmb τ θ →
        archM V θ δ = δ₀.1.map τ := by
  obtain ⟨δ₀, -, he⟩ := hδ
  have he' : ∀ i j, (matHom V δ).1 i j = (1 : AF D.host.F) ⊗ₜ δ₀.1 i j := fun i j =>
    (congrArg (fun x : GL (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E) => x.1 i j) he).symm
  refine ⟨δ₀, fun τ θ hθ => ?_⟩
  ext i j
  change θ (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) ((matHom V δ).1 i j)) = _
  rw [he', Algebra.TensorProduct.map_tmul, map_one]
  exact hθ.1 _

theorem exp_unitary_of_lie {n : ℕ} {J X : Matrix (Fin n) (Fin n) ℂ} (hJ : IsUnit J.det) (hX : Xᴴ * J + J * X = 0) :
    NormedSpace.exp X ∈ Formalism.QuantumDeterminants.UH J := by
  have h1 : Xᴴ = J * (-X) * J⁻¹ := by
    rw [mul_neg, ← eq_neg_of_add_eq_zero_left hX, mul_nonsing_inv_cancel_right _ _ hJ]
  change (NormedSpace.exp X)ᴴ * J * NormedSpace.exp X = J
  rw [← Matrix.exp_conjTranspose, h1, Matrix.exp_conj _ _ ((isUnit_iff_isUnit_det J).2 hJ),
    nonsing_inv_mul_cancel_right _ _ hJ, Matrix.mul_assoc,
    ← Matrix.exp_add_of_commute _ _ (Commute.refl X).neg_left, neg_add_cancel, NormedSpace.exp_zero, Matrix.mul_one]

theorem negFirst_of_orth (V : HSp D) (X : Data D.host.E V.rank) (hW : ModelW V rfl X)
    (hΨ : ∀ ρ, tauE D ρ ∈ X.Ψ) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hO : IsOrthogonalFrame X x₀) :
    NegFirst V X.p0 fun ρ => x₀ (tauE D ρ) := by
  intro ρ
  have h := hO _ (hΨ ρ)
  have hG : X.Gm = -V.gram.transpose := by
    rw [hW.1]; rfl
  ext b a
  have h1 := congrFun (congrFun h a) b
  have h2 : ((x₀ (tauE D ρ))ᴴ * gramAt D V ρ * x₀ (tauE D ρ)) b a =
      -ReciprocityTheory.ChartRestriction.G.FD.gram (tauE D ρ) X.Gm (x₀ (tauE D ρ)) a b := by
    simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, hG, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      gramAt, Matrix.map_apply, Matrix.neg_apply, Matrix.transpose_apply, map_neg, Finset.sum_mul,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [starRingEnd_apply]
    ring
  show ((x₀ (tauE D ρ))ᴴ * gramAt D V ρ * x₀ (tauE D ρ)) b a = _
  rw [h2, h1]
  by_cases hab : a = b
  · subst hab
    simp only [Matrix.diagonal_apply_eq, sgn]
    split_ifs <;> simp
  · rw [Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ (Ne.symm hab), neg_zero]

theorem NegFirst.det_unit {V : HSp D} {q : ℕ} {x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (h : NegFirst V q x) (ρ : D.what₂.Tau) : IsUnit (x ρ).det := by
  have h1 := congrArg Matrix.det (h ρ)
  rw [Matrix.det_mul, Matrix.det_diagonal] at h1
  rw [isUnit_iff_ne_zero]
  intro h0
  rw [h0, mul_zero] at h1
  refine (Finset.prod_ne_zero_iff.2 fun c _ => ?_) h1.symm
  split_ifs <;> simp

theorem baseDict_of_frames (V : HSp D) {r : ℕ} (hr : V.rank = r) {Comp : Type} (X : Comp → Data D.host.E r)
    (dict : GA D V → Σ k, Frame (X k).Ψ r) (Kf : Subgroup (GA D V))
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ)
    (th th' : ∀ k, (X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (hth : ∀ k τ, IsInfEmb τ.1 (th k τ)) (hth' : ∀ k τ, IsInfEmb τ.1 (th' k τ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (hΨ : ∀ k τ, τ ∈ (X k).Ψ ↔ ∃ ρ, τ = tauE D ρ) (hW : ∀ k, ModelW V hr (X k)) (hO : ∀ k, IsOrthogonalFrame (X k) x₀)
    (hD : DictIsUnif V dict Kf th hr)
    (hL : ∀ h, ∃ γ ∈ GQ V, ∀ τ : (X (dict h).1).Ψ, mat (dict h).2 τ =
      Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th' (dict h).1 τ) (γ * h)) * x₀ τ.1) :
    ∃ x, BaseDict θ V hr X dict Kf x := by
  subst hr
  have hre : ∀ M : Matrix (Fin V.rank) (Fin V.rank) ℂ,
      Matrix.reindex (finCongr (rfl : V.rank = V.rank)) (finCongr rfl) M = M := fun M => rfl
  obtain ⟨-, -, ⟨x0, hx0, hmul⟩, -, -, hfib⟩ := hD
  have e1 : ∀ k (τ : (X k).Ψ) ρ, τ.1 = tauE D ρ → th k τ = θ ρ := fun k τ ρ e =>
    GlobalTheory.SmoothForms.RealPts.infEmb_unique τ.1 _ _ (hth k τ) (e ▸ hθ ρ)
  have e2 : ∀ k (τ : (X k).Ψ) ρ, τ.1 = tauE D ρ → th' k τ = θ ρ := fun k τ ρ e =>
    GlobalTheory.SmoothForms.RealPts.infEmb_unique τ.1 _ _ (hth' k τ) (e ▸ hθ ρ)
  have hN : ∀ k, NegFirst V (X k).p0 fun ρ => x₀ (tauE D ρ) := fun k =>
    negFirst_of_orth V (X k) (hW k) (fun ρ => (hΨ k _).2 ⟨ρ, rfl⟩) x₀ (hO k)
  have hL' : ∀ h k (y : Frame (X k).Ψ V.rank), dict h = ⟨k, y⟩ → ∃ γ ∈ GQ V, ∀ ρ (τ : (X k).Ψ), τ.1 = tauE D ρ →
      mat y τ = archM V (θ ρ) (γ * h) * x₀ (tauE D ρ) := by
    intro h k y e
    have := hL h
    rw [e] at this
    obtain ⟨γ, hγ, H⟩ := this
    refine ⟨γ, hγ, fun ρ τ eτ => ?_⟩
    have := H τ
    rw [hre, e2 k τ ρ eτ, eτ] at this
    exact this
  have hmul' : ∀ g k (y : Frame (X k).Ψ V.rank), dict g = ⟨k, y⟩ → ∀ u ∈ GinfC V, ∃ γ' ∈ (X k).Γ,
      dict (g * u) = ⟨k, lact γ' (rmul y (archMat V th rfl x0 u k))⟩ := by
    intro g k y e u hu
    have := hmul g u hu
    rw [e] at this
    exact this
  have hA : ∀ k (τ : (X k).Ψ) ρ, τ.1 = tauE D ρ → ∀ u, mat (archMat V th rfl x0 u k) τ =
      (mat (x0 k) τ)⁻¹ * archM V (θ ρ) u * mat (x0 k) τ := by
    intro k τ ρ e u
    rw [← e1 k τ ρ e]
    rfl
  have hcen : ∀ k (τ : (X k).Ψ) ρ, τ.1 = tauE D ρ → ∀ u, mat (archMat V th rfl x0 u k) τ =
      (x₀ (tauE D ρ))⁻¹ * archM V (θ ρ) u * x₀ (tauE D ρ) := by
    intro k τ ρ e
    obtain ⟨g0, hg0⟩ := (hx0 k).2
    obtain ⟨γ0, hγ0, H0⟩ := hL' g0 k _ hg0
    have H0' := H0 ρ τ e
    set a := archM V (θ ρ) (γ0 * g0) with ha
    set x := x₀ (tauE D ρ) with hx
    have hxu : IsUnit x.det := (hN k).det_unit ρ
    have hau : IsUnit a.det := archM_det_unit _ _ _
    have haxu : IsUnit (a * x).det := by rw [Matrix.det_mul]; exact hau.mul hxu
    haveI : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.injective.countable
    haveI : Countable (Matrix (Fin V.rank) (Fin V.rank) D.host.E) :=
      inferInstanceAs (Countable (Fin V.rank → Fin V.rank → D.host.E))
    have hc : ∀ w, w * a = a * w := by
      refine GlobalTheory.central_of_countable_commutators_unitary V.rank (gramAt D V ρ) a
        (Set.range fun M : Matrix (Fin V.rank) (Fin V.rank) D.host.E => M.map (tauE D ρ))
        (GlobalTheory.SmoothForms.RealPts.gramAt_herm V ρ) (GlobalTheory.SmoothForms.RealPts.gramAt_unit V ρ) hau
        (Set.countable_range _) fun Z hZ t => ?_
      have hZ' : Zᴴ * gramAt D V ρ + gramAt D V ρ * Z = 0 := hZ
      have hU : NormedSpace.exp (t • Z) ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ) := by
        refine exp_unitary_of_lie (GlobalTheory.SmoothForms.RealPts.gramAt_unit V ρ) ?_
        rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hZ', smul_zero]
      obtain ⟨u, hu, huU⟩ := (GlobalTheory.SmoothForms.RealPts.glue θ hθ V).2
        (fun ρ' => if ρ' = ρ then NormedSpace.exp (t • Z) else 1) (fun ρ' => by
          by_cases h : ρ' = ρ
          · subst h; simpa using hU
          · simp [h, Formalism.QuantumDeterminants.UH])
      have hUu : archM V (θ ρ) u = NormedSpace.exp (t • Z) := by
        have := huU ρ
        rw [if_pos rfl] at this
        exact this
      have hinv : NormedSpace.exp (t • Z) * NormedSpace.exp (-(t • Z)) = 1 := by
        rw [← Matrix.exp_add_of_commute _ _ (Commute.refl (t • Z)).neg_right]
        simp
      generalize NormedSpace.exp (t • Z) = U at hUu hinv
      generalize NormedSpace.exp (-(t • Z)) = U' at hinv
      obtain ⟨γ', -, h1⟩ := hmul' g0 k _ hg0 u hu
      obtain ⟨γ'', hγ'', h2⟩ := hL' _ k _ h1
      have h3 := h2 ρ τ e
      obtain ⟨δ, hδ⟩ := archM_rational V (γ'' * γ0⁻¹) (mul_mem hγ'' (inv_mem hγ0))
      have h4 : γ'' * (g0 * u) = (γ'' * γ0⁻¹) * (γ0 * g0) * u := by group
      rw [h4, archM_mul', archM_mul', hδ _ _ (hθ ρ), ← ha, hUu] at h3
      change γ'.1.map τ.1 * (mat (x0 k) τ * mat (archMat V th rfl x0 u k) τ) = _ at h3
      rw [hA k τ ρ e, H0', hUu, e, ← Matrix.mul_assoc (a * x), ← Matrix.mul_assoc (a * x),
        Matrix.mul_nonsing_inv _ haxu, Matrix.one_mul, ← hx] at h3
      have h5 : γ'.1.map (tauE D ρ) * (U * a) = δ.1.map (tauE D ρ) * a * U := by
        have := congrArg (· * x⁻¹) h3
        simpa only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hxu, Matrix.mul_one] using this
      refine ⟨(γ'⁻¹).1 * δ.1, ?_⟩
      have h6 : (γ'⁻¹).1.map (tauE D ρ) * γ'.1.map (tauE D ρ) = 1 := by
        rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      show ((γ'⁻¹).1 * δ.1).map (tauE D ρ) = _
      rw [Matrix.map_mul, ← Matrix.one_mul (U * a), ← h6, Matrix.mul_assoc _ _ (U * a), h5]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc U, hinv, Matrix.one_mul, Matrix.mul_nonsing_inv _ hau, Matrix.mul_one]
    intro u
    rw [hA k τ ρ e, H0', Matrix.mul_inv_rev, Matrix.mul_assoc x⁻¹, Matrix.mul_assoc x⁻¹, Matrix.mul_assoc x⁻¹,
      Matrix.mul_assoc a⁻¹, ← Matrix.mul_assoc _ a, hc, Matrix.mul_assoc a, ← Matrix.mul_assoc a⁻¹,
      Matrix.nonsing_inv_mul _ hau, Matrix.one_mul]
  refine ⟨fun ρ => x₀ (tauE D ρ), fun k => ⟨⟨hΨ k, hW k⟩, hN k, ?_⟩, fun h => ?_, hfib⟩
  · obtain ⟨g, hg⟩ := (hx0 k).2
    exact ⟨g, by rw [hg]⟩
  · obtain ⟨γ, hγ, H⟩ := hL' h (dict h).1 (dict h).2 rfl
    refine ⟨γ, hγ, fun ρ τ e => H ρ τ e, fun u hu => ?_⟩
    obtain ⟨γ', hγ', h1⟩ := hmul h u hu
    refine ⟨γ', hγ', _, h1, fun ρ τ e => ?_⟩
    change mat (dict h).2 τ * mat (archMat V th rfl x0 u (dict h).1) τ =
      archM V (θ ρ) (γ * h * u) * x₀ (tauE D ρ)
    rw [hcen _ τ ρ e, H ρ τ e, archM_mul' V _ (γ * h) u]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (x₀ _), Matrix.mul_nonsing_inv _ ((hN (dict h).1).det_unit ρ), Matrix.one_mul]

theorem baseDict_core : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ θ : InfFam D, IsInfFam θ → ∃ (hr : (T.V j σ).rank = D.R.r) (x₀ : D.what₂.Tau → Matrix (Fin (T.V j σ).rank) (Fin (T.V j σ).rank) ℂ), BaseDict θ (T.V j σ) hr (T.U j σ).X (T.dict j σ) (T.Kf j σ) x₀ := by
  intro D T h j hj σ hσ θ hθ
  obtain ⟨th, hr, hth, hD⟩ := h.dictU j hj σ hσ
  obtain ⟨hr', hW⟩ := h.modelW j hj σ hσ
  obtain ⟨hr'', g, e, F, ik, φ, th', -, -, hth', -, hL⟩ := h.adPin j hj σ hσ
  have hU := (h.unf j hj σ hσ).2.1
  have hin : ∀ k ρ, tauE D ρ ∈ ((T.U j σ).X k).Ψ := fun k ρ => ((hU k).2 _).2 (h.pins.1.2.2.2 ρ)
  refine ⟨hr, baseDict_of_frames _ hr _ _ _ θ hθ th th' hth hth' (T.x₀ j σ) (fun k τ => ⟨fun hτ => ?_, ?_⟩) hW
    (h.familyUniformisationBasePointOrthogonal j hj σ hσ) hD fun g => ?_⟩
  · obtain ⟨ρ, hρ⟩ := (GlobalTheory.SmoothForms.RealPts.tauE_cm D τ).2 (by
      rintro ⟨ρ, hρ⟩
      exact (((T.U j σ).X k).cmType τ).1 hτ (hρ ▸ hin k ρ))
    exact ⟨ρ, hρ.symm⟩
  · rintro ⟨ρ, rfl⟩
    exact hin k ρ
  · obtain ⟨γ, hγ, -, -, H⟩ := hL g
    exact ⟨γ, hγ, H⟩

end GlobalTheory.HolRead
end


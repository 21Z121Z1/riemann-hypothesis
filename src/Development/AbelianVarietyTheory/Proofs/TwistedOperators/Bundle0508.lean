import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0497
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0253
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0082
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0438
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0452
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0481
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0451
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPlacewiseTripleSpacesOfSeesaw
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0500
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteBranchingUpq

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EmbRelAtRealPlaceOfUnitaryEmbedding
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.EmbAtPlace

variable {D : D7}

theorem mat_ext {m n : Type*} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ Formalism.L2.Theta.AE D}
    (hσ : GlobalTheory.FockCompare.Chart θ σ) {M N : Matrix m n (Formalism.L2.Theta.AE D)}
    (h1 : M.map (Formalism.L2.Theta.finPart D) = N.map (Formalism.L2.Theta.finPart D))
    (h2 : ∀ τ, M.map (fun z => θ τ (Formalism.L2.Theta.infPart D z)) = N.map (fun z => θ τ (Formalism.L2.Theta.infPart D z))) :
    M = N := by
  ext i j
  refine sub_eq_zero.1 (hσ.ext _ ?_ fun τ => ?_)
  · rw [RingHom.map_sub, sub_eq_zero]; exact congrFun (congrFun h1 i) j
  · rw [RingHom.map_sub, RingHom.map_sub, sub_eq_zero]; exact congrFun (congrFun (h2 τ) i) j

theorem vec_ext {n : Type*} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ Formalism.L2.Theta.AE D}
    (hσ : GlobalTheory.FockCompare.Chart θ σ) {v w : n → Formalism.L2.Theta.AE D}
    (h1 : ∀ i, Formalism.L2.Theta.finPart D (v i) = Formalism.L2.Theta.finPart D (w i))
    (h2 : ∀ τ i, θ τ (Formalism.L2.Theta.infPart D (v i)) = θ τ (Formalism.L2.Theta.infPart D (w i))) : v = w := by
  funext i
  refine sub_eq_zero.1 (hσ.ext _ ?_ fun τ => ?_)
  · rw [RingHom.map_sub, sub_eq_zero]; exact h1 i
  · rw [RingHom.map_sub, RingHom.map_sub, sub_eq_zero]; exact h2 τ i

theorem theta_incA {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (e : D.host.E) :
    θ τ (Formalism.L2.Theta.infPart D (incA D e)) = tauE D τ e := by
  have : Formalism.L2.Theta.infPart D (incA D e) = (1 : Ainf D.host.F) ⊗ₜ[D.host.F] e := by
    simp [Formalism.L2.Theta.infPart, incA, inclR]
  rw [this]; exact (hθ τ).1 e

end GlobalTheory.EmbAtPlace

namespace GlobalTheory.EmbAtPlace

theorem embRel_atTau : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (τ : D.what₂.Tau)
    (h : Matrix (Fin A.rank) (Fin A.rank) ℂ) (g : Matrix (Fin B.rank) (Fin B.rank) ℂ), h ∈ Formalism.QuantumDeterminants.UH (gramAt D A τ) →
    g ∈ Formalism.QuantumDeterminants.UH (gramAt D B τ) → GlobalTheory.RealBessel.IsEmb (gramAt D B τ) ((frameMat B A ι).map (tauE D τ)) g h →
    EmbRel B A ι (atTau θ B τ g) (atTau θ A τ h) := by
  classical
  intro D θ hθ A B ι τ h g hh hg hE
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hX := GlobalTheory.PointAtPlaceHom.atTau_spec hθ B τ hg
  have hY := GlobalTheory.PointAtPlaceHom.atTau_spec hθ A τ hh
  have fX : (matHom B (atTau θ B τ g)).1.map (Formalism.L2.Theta.finPart D) = 1 :=
    (congrArg (fun k : GL (Fin B.rank) (Af D.host.F ⊗[D.host.F] D.host.E) => k.val) (MonoidHom.mem_ker.1 hX.1)).trans Units.val_one
  have fY : (matHom A (atTau θ A τ h)).1.map (Formalism.L2.Theta.finPart D) = 1 :=
    (congrArg (fun k : GL (Fin A.rank) (Af D.host.F ⊗[D.host.F] D.host.E) => k.val) (MonoidHom.mem_ker.1 hY.1)).trans Units.val_one
  have iX : ∀ τ', (matHom B (atTau θ B τ g)).1.map (fun z => θ τ' (Formalism.L2.Theta.infPart D z)) =
      if τ' = τ then g else 1 := fun τ' => by
    split_ifs with e
    · subst e; exact hX.2.1
    · exact hX.2.2 τ' e
  have iY : ∀ τ', (matHom A (atTau θ A τ h)).1.map (fun z => θ τ' (Formalism.L2.Theta.infPart D z)) =
      if τ' = τ then h else 1 := fun τ' => by
    split_ifs with e
    · subst e; exact hY.2.1
    · exact hY.2.2 τ' e
  have iF : ∀ τ', ((frameMat B A ι).map (incA D)).map (fun z => θ τ' (Formalism.L2.Theta.infPart D z)) =
      (frameMat B A ι).map (tauE D τ') := fun τ' => by
    rw [Matrix.map_map]; congr 1; funext e; exact GlobalTheory.EmbAtPlace.theta_incA hθ τ' e
  refine ⟨?_, fun x hx => ?_⟩
  · refine GlobalTheory.EmbAtPlace.mat_ext hσ ?_ fun τ' => ?_
    · rw [Matrix.map_mul, Matrix.map_mul, fX, fY, Matrix.one_mul, Matrix.mul_one]
    · let φ : Formalism.L2.Theta.AE D →+* ℂ := (θ τ').comp (Formalism.L2.Theta.infPart D)
      change Matrix.map (_ * _) ⇑φ = Matrix.map (_ * _) ⇑φ
      rw [Matrix.map_mul, Matrix.map_mul]
      change (matHom B (atTau θ B τ g)).1.map (fun z => θ τ' (Formalism.L2.Theta.infPart D z)) *
          ((frameMat B A ι).map (incA D)).map (fun z => θ τ' (Formalism.L2.Theta.infPart D z)) =
        ((frameMat B A ι).map (incA D)).map (fun z => θ τ' (Formalism.L2.Theta.infPart D z)) *
          (matHom A (atTau θ A τ h)).1.map (fun z => θ τ' (Formalism.L2.Theta.infPart D z))
      rw [iX, iY, iF]
      split_ifs with e
      · subst e; exact hE.1
      · rw [Matrix.one_mul, Matrix.mul_one]
  · refine GlobalTheory.EmbAtPlace.vec_ext hσ (fun i => ?_) fun τ' i => ?_
    · rw [RingHom.map_mulVec, fX, Matrix.one_mulVec]; rfl
    · let φ : Formalism.L2.Theta.AE D →+* ℂ := (θ τ').comp (Formalism.L2.Theta.infPart D)
      change φ _ = φ _
      rw [RingHom.map_mulVec]
      change ((matHom B (atTau θ B τ g)).1.map (fun z => θ τ' (Formalism.L2.Theta.infPart D z)) *ᵥ
        fun j => θ τ' (Formalism.L2.Theta.infPart D (incA D (x j)))) i = θ τ' (Formalism.L2.Theta.infPart D (incA D (x i)))
      simp only [GlobalTheory.EmbAtPlace.theta_incA hθ]
      rw [iX]
      split_ifs with e
      · subst e
        have h0 : (((frameMat B A ι).map (tauE D τ'))ᴴ * gramAt D B τ') *ᵥ (fun j => tauE D τ' (x j)) = 0 := by
          have hm : ((frameMat B A ι).map (tauE D τ'))ᴴ * gramAt D B τ' =
              (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat B A ι) * B.gram).map (tauE D τ') := by
            rw [Matrix.map_mul]
            congr 1
            ext a b
            simp only [Matrix.conjTranspose_apply, Matrix.map_apply, Formalism.UG.cT, Matrix.transpose_apply]
            exact (Formalism.IndefR.Eqv.tauE_star D τ' _).symm
          rw [hm]
          funext i
          have := RingHom.map_mulVec (tauE D τ') (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat B A ι) * B.gram) x i
          simp only [Function.comp_def] at this
          rw [← this, hx]
          simp
        exact congrFun (hE.2 _ h0) i
      · rw [Matrix.one_mulVec]

end GlobalTheory.EmbAtPlace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EmbeddingColumnLatticeIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.UnitaryEmbeddingLine

variable {D : D7}

theorem tmul_mul_inc (α : AF D.host.F) (b x : D.host.E) :
    (α ⊗ₜ[D.host.F] b : AE D) * incA D x = α ⊗ₜ[D.host.F] (b * x) := by
  change (α ⊗ₜ[D.host.F] b) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] x : AE D) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem exists_coeff {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (hε : ε ≠ 0) (p : Fin c) :
    ∃ r : Fin B.rank → D.host.E, ∀ (y : Fin A.rank → D.host.E) (u : Fin c → D.host.E),
      r ⬝ᵥ (frameMat B A d.ι *ᵥ y + d.a *ᵥ u) = u p := by
  have hG : B.gramᴴ = B.gram := Matrix.ext fun i j => B.herm.eq _ _
  have h1 : d.aᴴ * B.gram * d.a = antiDiagonalSignGramMatrix c ε := d.gram
  have h2 : (frameMat B A d.ι)ᴴ * B.gram * d.a = 0 := d.perp
  have h3 : d.aᴴ * B.gram * frameMat B A d.ι = 0 := by
    have := congrArg Matrix.conjTranspose h2
    rw [Matrix.conjTranspose_zero, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hG,
      Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc] at this
    exact this
  have hκ : antiDiagonalSignGramMatrix c ε p.rev p ≠ 0 := by
    have := p.2
    have e : p.rev.1 + p.1 + 1 = c := by rw [Fin.val_rev]; omega
    simp only [antiDiagonalSignGramMatrix, if_pos e]
    split_ifs
    · exact hε
    · exact one_ne_zero
  refine ⟨(antiDiagonalSignGramMatrix c ε p.rev p)⁻¹ • (d.aᴴ * B.gram) p.rev, fun y u => ?_⟩
  have e : (d.aᴴ * B.gram) p.rev ⬝ᵥ (frameMat B A d.ι *ᵥ y + d.a *ᵥ u) =
      ((d.aᴴ * B.gram) *ᵥ (frameMat B A d.ι *ᵥ y + d.a *ᵥ u)) p.rev := rfl
  rw [smul_dotProduct, e, mulVec_add, mulVec_mulVec, mulVec_mulVec, h1, h3, zero_mulVec, zero_add]
  have e2 : (antiDiagonalSignGramMatrix c ε *ᵥ u) p.rev = antiDiagonalSignGramMatrix c ε p.rev p * u p := by
    show ∑ q, antiDiagonalSignGramMatrix c ε p.rev q * u q = _
    refine Finset.sum_eq_single p (fun q _ hq => ?_) (by simp)
    have := p.2
    have hne : ¬ (p.rev.1 + q.1 + 1 = c) := by
      intro h; apply hq; apply Fin.ext; rw [Fin.val_rev] at h; omega
    simp only [antiDiagonalSignGramMatrix, if_neg hne, zero_mul]
  rw [e2, smul_eq_mul, inv_mul_cancel_left₀ hκ]

def formHom {R : Type} [CommRing R] {n : ℕ} (r : Fin n → R) : (Fin n → R) →+ R where
  toFun y := ∑ k, y k * r k
  map_zero' := by simp
  map_add' x y := by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

def lineHom {R : Type} [CommRing R] {n : ℕ} (a : Fin n → R) : R →+ (Fin n → R) where
  toFun s := fun k => s * a k
  map_zero' := by funext k; simp
  map_add' x y := by funext k; simp only [Pi.add_apply, add_mul]

theorem form_line {K R : Type} [CommRing K] [CommRing R] (f : K →+* R) {n : ℕ} (r a : Fin n → K) (h : r ⬝ᵥ a = 1) (s : R) :
    formHom (fun k => f (r k)) (fun k => s * f (a k)) = s := by
  show ∑ k, s * f (a k) * f (r k) = s
  simp only [mul_assoc, ← map_mul]
  rw [← Finset.mul_sum, ← map_sum]
  have : ∑ k, a k * r k = 1 := by
    rw [← h, dotProduct]; exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [this, map_one, mul_one]

theorem col_eq {K : Type} [CommRing K] {n k c : ℕ} (M : Matrix (Fin n) (Fin k) K) (a : Matrix (Fin n) (Fin c) K) (p : Fin c)
    (b : K) : (fun i => b * a i p) = M *ᵥ 0 + a *ᵥ Pi.single p b := by
  funext k; simp [mul_comm]

theorem line_mp {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → GlobalTheory.SeeSaw.FI D) (p : Fin c) (v : GlobalTheory.FinPl.Pl D)
    (S : Set D.host.E) (I : GlobalTheory.SeeSaw.FI D) (hε : ε ≠ 0) (hI : ∀ a ∈ S, ∀ b ∈ 𝔟 p, a * b ∈ I) (s : AE D)
    (h : (fun k => s * incA D (d.a k p)) ∈ GlobalTheory.FinPl.latMul B S (d.lat Λ 𝔟) (· = v)) : s ∈ GlobalTheory.SeeSaw.idV I v := by
  obtain ⟨r, hr⟩ := exists_coeff d hε p
  have key : GlobalTheory.FinPl.latMul B S (d.lat Λ 𝔟) (· = v) ≤ (GlobalTheory.SeeSaw.idV I v).comap (formHom fun k => incA D (r k)) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, hαv, a, ha, x, ⟨y0, -, u, hu, hx⟩, rfl⟩
    have e : ∑ k, ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * x k) : AE D) * incA D (r k) =
        (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * u p) := by
      rw [Finset.sum_congr rfl fun k _ => tmul_mul_inc (pairA D.host.F 0 α) (a * x k) (r k),
        ← TensorProduct.tmul_sum, ← hr y0 u, ← hx, dotProduct, Finset.mul_sum]
      exact congrArg _ (Finset.sum_congr rfl fun k _ => by ring)
    have h2 : (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * u p) ∈ GlobalTheory.SeeSaw.idV I v :=
      AddSubgroup.subset_closure ⟨α, hα, hαv, _, hI a ha _ (hu p), rfl⟩
    rw [← e] at h2
    exact h2
  have h1 := hr 0 (Pi.single p 1)
  rw [← col_eq, Pi.single_eq_same] at h1
  simp only [one_mul] at h1
  have := AddSubgroup.mem_comap.1 (key h)
  rwa [form_line (incA D) r (fun k => d.a k p) h1 s] at this

theorem line_mpr {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → GlobalTheory.SeeSaw.FI D) (p : Fin c) (v : GlobalTheory.FinPl.Pl D)
    (S : Set D.host.E) (I : GlobalTheory.SeeSaw.FI D)
    (hI' : ∀ C : D.host.E → Prop, (∀ a ∈ S, ∀ b ∈ 𝔟 p, C (a * b)) → (∀ x y, C x → C y → C (x + y)) → ∀ z ∈ I, C z)
    (s : AE D) (h : s ∈ GlobalTheory.SeeSaw.idV I v) :
    (fun k => s * incA D (d.a k p)) ∈ GlobalTheory.FinPl.latMul B S (d.lat Λ 𝔟) (· = v) := by
  have key : GlobalTheory.SeeSaw.idV I v ≤ (GlobalTheory.FinPl.latMul B S (d.lat Λ 𝔟) (· = v)).comap (lineHom fun k => incA D (d.a k p)) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, hαv, z, hz, rfl⟩
    refine hI' (fun z => ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] z : AE D) ∈
      (GlobalTheory.FinPl.latMul B S (d.lat Λ 𝔟) (· = v)).comap (lineHom fun k => incA D (d.a k p))) ?_ ?_ z hz
    · intro a ha b hb
      refine AddSubgroup.mem_comap.2 (AddSubgroup.subset_closure ⟨α, hα, hαv, a, ha, fun k => b * d.a k p,
        ⟨0, Λ.zero_mem, Pi.single p b, fun q => ?_, col_eq _ _ p b⟩, ?_⟩)
      · by_cases hq : q = p
        · subst hq; rwa [Pi.single_eq_same]
        · rw [Pi.single_eq_of_ne hq]; exact (𝔟 q).zero_mem
      · funext k
        exact (tmul_mul_inc _ _ _).trans (congrArg _ (mul_assoc _ _ _))
    · intro x y hx hy
      rw [TensorProduct.tmul_add]
      exact add_mem hx hy
  exact AddSubgroup.mem_comap.1 (key h)

theorem line_gen {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → GlobalTheory.SeeSaw.FI D) (p : Fin c) (v : GlobalTheory.FinPl.Pl D)
    (S : Set D.host.E) (I : GlobalTheory.SeeSaw.FI D) (hε : ε ≠ 0) (hI : ∀ a ∈ S, ∀ b ∈ 𝔟 p, a * b ∈ I)
    (hI' : ∀ C : D.host.E → Prop, (∀ a ∈ S, ∀ b ∈ 𝔟 p, C (a * b)) → (∀ x y, C x → C y → C (x + y)) → ∀ z ∈ I, C z)
    (s : AE D) :
    (fun k => s * incA D (d.a k p)) ∈ GlobalTheory.FinPl.latMul B S (d.lat Λ 𝔟) (· = v) ↔ s ∈ GlobalTheory.SeeSaw.idV I v :=
  ⟨line_mp d Λ 𝔟 p v S I hε hI s, line_mpr d Λ 𝔟 p v S I hI' s⟩

theorem embedding_line_mem_lattice_iff : ∀ {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε), ε ≠ 0 → ∀ (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → GlobalTheory.SeeSaw.FI D) (p : Fin c) (v : GlobalTheory.FinPl.Pl D) (s : AE D), (((fun k => s * incA D (d.a k p)) ∈ latV B (d.lat Λ 𝔟) (· = v) ↔ s ∈ GlobalTheory.SeeSaw.idV (𝔟 p) v) ∧ ((fun k => s * incA D (d.a k p)) ∈ latA B (d.lat Λ 𝔟) (· = v) ↔ s ∈ GlobalTheory.SeeSaw.idV (D.host.AA * 𝔟 p) v)) := by
  intro D A B c ε d hε Λ 𝔟 p v s
  refine ⟨line_gen d Λ 𝔟 p v {1} (𝔟 p) hε ?_ ?_ s, line_gen d Λ 𝔟 p v {a | a ∈ D.host.AA} _ hε ?_ ?_ s⟩
  · rintro a rfl b hb; rwa [one_mul]
  · intro C h _ z hz
    have := h 1 rfl z hz
    rwa [one_mul] at this
  · intro a ha b hb; exact FractionalIdeal.mul_mem_mul ha hb
  · intro C h h' z hz
    exact FractionalIdeal.mul_induction_on hz h h'

end GlobalTheory.AscFin.UnitaryEmbeddingLine

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCompactMeetsBesselTopRationalOrbits
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)

namespace GlobalTheory.BesCover

open GlobalTheory.Per GlobalTheory.Per.Inhab

theorem exists_compact_cover {D : D7} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} {ρ : ℕ}
    {e : Matrix (Fin B.rank) (Fin ρ) D.host.E} (he : IsIsoSub B e) (hι : HSpace.IsIsomEmb A B ι) (hA : IsAniso A)
    (hnorm : ∀ δ γ, EmbRel B A ι δ γ → ∀ n ∈ NFlag B e, δ * n * δ⁻¹ ∈ NFlag B e)
    {t : GA D A → GA D B} (ht : ∀ h, EmbRel B A ι (t h) h) :
    ∃ Ω : Set (GA D B), IsCompact Ω ∧ ∀ (h : GA D A) (n : NFlag B e), ∃ γ ∈ GQ B, γ * ((n : GA D B) * t h) ∈ Ω := by
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.Mem.AnisoQuotient.exists_compact D A hA
  obtain ⟨K', hK', hcov'⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D B _ _ he).1
  obtain ⟨s, hc, hs, hq⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D B A ι hι
  obtain ⟨-, -, -, -, _, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  obtain rfl : t = s := funext fun h => (hs h _).1 (ht h)
  refine ⟨(fun q : GA D A × NFlag B e => (q.2 : GA D B) * s q.1) '' (K ×ˢ K'),
    (hK.prod hK').image ((continuous_subtype_val.comp continuous_snd).mul (hc.comp continuous_fst)), fun g n => ?_⟩
  obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov g
  obtain ⟨γ', hγ', k', hk', e⟩ := hcov' ⟨_, hnorm _ γ⁻¹ ((hs _ _).2 rfl) n n.2⟩
  have e' : s γ⁻¹ * n * (s γ⁻¹)⁻¹ = (γ' : GA D B) * k' := congrArg Subtype.val e
  have e1 : (n : GA D B) = s γ * (γ' * k') * (s γ)⁻¹ := by
    rw [← e']; simp only [map_inv, inv_inv, mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
  refine ⟨(s γ * γ')⁻¹, inv_mem (mul_mem (hq γ hγ) hγ'), (k, k'), ⟨hk, hk'⟩, ?_⟩
  rw [e1]
  simp only [map_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left]

theorem bplus_cover : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G), M.IsRow →
    ∃ Ω : Set (GA D (G.V (.grid D.R.m 0))), IsCompact Ω ∧ ∀ (h : GA D (G.V (.top 0))) (n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e),
      ∃ γ ∈ GQ (G.V (.grid D.R.m 0)), γ * ((n : GA D (G.V (.grid D.R.m 0))) * embTop G h) ∈ Ω := by
  intro D T L sc G W M _
  have hV := G.isV (X := .top 0) (Nat.zero_le _) (fun j e => by cases e)
  have hA : IsAniso (G.V (.top 0)) := GlobalTheory.Per.isAniso_of_posDef hV.sigOK fun τ => by
    rw [hV.sig τ, hV.rank]; simp [Node.neg]
  have hι := (G.rowDec 0 (by have := D.R.two_le_m; omega)).isom
  have hs : ∀ h, EmbRel _ _ (G.rowDec 0 (by have := D.R.two_le_m; omega)).ι (embTop G h) h :=
    fun h => (embRel_iff _ h _).2 rfl
  exact exists_compact_cover G.besTop.e_iso hι hA
    (fun δ γ h n hn => (GlobalTheory.BesselChar.besChar_conj W.ψ G.besTop δ γ h n hn).1) hs

end GlobalTheory.BesCover
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeckeElementLatticeBetweenPrimeMulSplit
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

namespace GlobalTheory.HeckeLocStep

open Formalism.L2.Theta
open scoped TensorProduct

theorem smul_mem_hat (D : D7) {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    {a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E} (ha : a ∈ intAE D)
    {y : Fin n → GlobalTheory.AdLat.RA D.host.F D.host.E} (hy : y ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E))) :
    a • y ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E)) := by
  induction ha using AddSubgroup.closure_induction generalizing y with
  | mem w hw =>
    obtain ⟨b, hb, x, rfl⟩ := hw
    induction hy using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨c, hc, m, hm, rfl⟩ := hz
      refine AddSubgroup.subset_closure ⟨b * c, fun v => ?_, x • m, L.smul_mem x hm, ?_⟩
      · exact mul_mem (hb v) (hc v)
      · funext i
        simp [Algebra.TensorProduct.tmul_mul_tmul]
        rfl
    | zero => rw [smul_zero]; exact zero_mem _
    | add z z' _ _ h h' => rw [smul_add]; exact add_mem h h'
    | neg z _ h => rw [smul_neg]; exact neg_mem h
  | zero => rw [zero_smul]; exact zero_mem _
  | add a b _ _ h h' => rw [add_smul]; exact add_mem (h hy) (h' hy)
  | neg a _ h => rw [neg_smul]; exact neg_mem (h hy)

end GlobalTheory.HeckeLocStep

namespace GlobalTheory.HeckeLocStep

open Formalism.L2.Theta
open scoped TensorProduct

theorem hat_mono {D : D7} {n : ℕ} {L L' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (h : L ≤ L') :
    GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E)) ≤ GlobalTheory.AdLat.hat D.host.F (L' : Set (Fin n → D.host.E)) := by
  refine AddSubgroup.closure_mono ?_
  rintro _ ⟨a, ha, x, hx, rfl⟩
  exact ⟨a, ha, x, h hx, rfl⟩

theorem span_smul_top {D : D7} {n : ℕ} (P : Formalism.L2.DIV.Pl D.host.E) (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (hL : Submodule.span D.host.E (L : Set (Fin n → D.host.E)) = ⊤) :
    Submodule.span D.host.E ((P.asIdeal • L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E)) = ⊤ := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
  have hx0' : ((x : D.host.E)) ≠ 0 := fun h => hx0 (RingOfIntegers.ext h)
  rw [eq_top_iff, ← hL, Submodule.span_le]
  intro w hw
  have hm : x • w ∈ (P.asIdeal • L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) := Submodule.smul_mem_smul hx hw
  have : w = (x : D.host.E)⁻¹ • (x • w) := by
    rw [← algebraMap_smul D.host.E x w]
    rw [smul_smul, inv_mul_cancel₀ (by simpa using hx0'), one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hm)

theorem mem_iff_ePart : ∀ (D : D7) (V : HSp D) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (g : GA D V)
    (M : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    Formalism.L2.NTheta.IsIdemAt e P → P.asIdeal • latG V g ≤ M → M ≤ latG V g →
    ∀ v ∈ latG V g, (v ∈ M ↔ finPart D e • finVec V v ∈ GlobalTheory.AdLat.hat D.host.F (M : Set (Fin V.rank → D.host.E))) := by
  intro D V P e g M he hPM hMΛ v hv
  obtain ⟨h1, h2, -, -, -, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D V g
  have hMfg : M.FG := by
    have hN : IsNoetherian (𝓞 D.host.E) (latG V g) := isNoetherian_of_fg_of_noetherian _ h1
    have hc := (IsNoetherian.noetherian (M.comap (latG V g).subtype)).map (latG V g).subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.2 hMΛ] at hc
  have hMsp : Submodule.span D.host.E (M : Set (Fin V.rank → D.host.E)) = ⊤ :=
    eq_top_iff.2 ((span_smul_top P _ h2).symm.le.trans (Submodule.span_mono hPM))
  have hrat := (GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E V.rank M hMfg hMsp).1
  have hint : finPart D e ∈ intAE D := GlobalTheory.SplitPlace.idem_mem he.1.1
  have hvM : ∀ {w}, w ∈ M → GlobalTheory.AdLat.fv D.host.F w ∈ GlobalTheory.AdLat.hat D.host.F (M : Set (Fin V.rank → D.host.E)) :=
    fun hw => (hrat _).2 hw
  constructor
  · intro hm
    exact smul_mem_hat D M hint (hvM hm)
  · intro h
    refine (hrat v).1 ?_
    have hΛ : GlobalTheory.AdLat.fv D.host.F v ∈ GlobalTheory.AdLat.hat D.host.F ((latG V g : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E)) :=
      ((GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E V.rank _ h1 h2).1 v).2 hv
    have h3 := hat_mono hPM (GlobalTheory.T.one_sub_idempotent_smul_mem_completion_prime_mul D P e V.rank (latG V g) he _ hΛ)
    have hsplit : GlobalTheory.AdLat.fv D.host.F v = finPart D e • finVec V v + (1 - finPart D e) • finVec V v := by
      rw [← add_smul, add_sub_cancel, one_smul]; rfl
    rw [hsplit]
    exact add_mem h h3

theorem mem_latG_iff (D : D7) (V : HSp D) (x : GA D V) (v : Fin V.rank → D.host.E) :
    v ∈ latG V x ↔ finVec V v ∈ latGHat V x := by
  obtain ⟨h1, h2, -, -, h5, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D V x
  rw [h5]
  exact ((GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E V.rank _ h1 h2).1 v).symm

theorem exists_hecke : ∀ (D : D7) (V : HSp D) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (ϖ : 𝓞 D.host.E) (k : ℕ) (g : GA D V)
    (M : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    P.asIdeal • latG V g ≤ M → M ≤ latG V g →
    M.toAddSubgroup.relIndex (latG V g).toAddSubgroup = Ideal.absNorm P.asIdeal ^ k →
    ∃ a₀ : GA D V, Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k a₀ ∧ latG V (g * a₀) ⊓ latG V g = M ∧
      (Formalism.L2.Col.conjPrime₂ P).asIdeal • latG V (g * a₀) ≤ latG V g := by
  intro D V P e ϖ k g M he h1 h2 hPM hMΛ hidx
  obtain ⟨a₀, hH, hloc⟩ := GlobalTheory.T.exists_heckeElement_idempotentPart_splitPlace_lattice D V P e ϖ k g M he h1 h2 hPM hMΛ hidx
  refine ⟨a₀, hH, ?_, GlobalTheory.T.conjPrime_smul_lattice_heckeElement_le D V P e ϖ k g a₀ he h1 h2 hH⟩
  have hint : finPart D e ∈ intAE D := GlobalTheory.SplitPlace.idem_mem he.1.1
  ext v
  rw [Submodule.mem_inf]
  constructor
  · rintro ⟨ha, hg⟩
    refine (mem_iff_ePart D V P e g M he hPM hMΛ v hg).2 ((hloc v hg).1 ?_)
    have := (mem_latG_iff D V (g * a₀) v).1 ha
    rw [(GlobalTheory.Member.latG_lattice_and_completion D V (g * a₀)).2.2.2.2.1] at this ⊢
    exact smul_mem_hat D _ hint this
  · intro hv
    have hg := hMΛ hv
    refine ⟨(mem_latG_iff D V (g * a₀) v).2 ?_, hg⟩
    have hsplit : finVec V v = finPart D e • finVec V v + (1 - finPart D e) • finVec V v := by
      rw [← add_smul, add_sub_cancel, one_smul]
    rw [hsplit]
    exact add_mem ((hloc v hg).2 ((mem_iff_ePart D V P e g M he hPM hMΛ v hg).1 hv))
      (GlobalTheory.T.hecke_element_keeps_one_sub_idempotent_part_lattice D V e ϖ k g a₀ he.1 hH _ ((mem_latG_iff D V g v).1 hg))

end GlobalTheory.HeckeLocStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPlacewiseTripleSpacesOfSeesawStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_placewise_triple_spaces_of_seesaw : ∀ (D : D7) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ p q : ℕ, (∀ τ, Formalism.UG.HasSignature (gramAt D W τ) (W.rank - p) p ∧ Formalism.UG.HasSignature (gramAt D W₁ τ) (W₁.rank - q) q ∧
      Formalism.UG.HasSignature (gramAt D X τ) (X.rank - (p + q)) (p + q)) →
    ∀ (e : Fin X.rank ≃ Fin (W.rank + W₁.rank)) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig →
    (∀ w, ∃ τ, ∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) →
    ∃ (V : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E W.rank) (V' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E W₁.rank)
      (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E (W.rank + W₁.rank)),
      V.J = (1 : D.host.E) • W.gram ∧ V'.J = (-1 : D.host.E) • W₁.gram ∧ Ws.J = D.host.xi0 • reindex e e X.gramᵀ ∧
      V.IsHerm D.sp.cm.sig Bs (W.rank - p) p ∧ V'.IsHerm D.sp.cm.sig Bs q (W₁.rank - q) ∧
      Ws.IsSkew D.sp.cm.sig Bs (W.rank + W₁.rank - (p + q)) (p + q) ∧
      ∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ V.θ w = A.cart τ ∧ V'.θ w = -A₁.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ) := by
  first | exact @GlobalTheory.PlaceSpaces.spaces_of_triple | exact GlobalTheory.PlaceSpaces.spaces_of_triple | (intros; apply GlobalTheory.PlaceSpaces.spaces_of_triple <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FormalDegreeLoweringWeightRatioLeStatement
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalDegree_loweringWeight_ratio_le : DegRatio := by
  first | exact @GlobalTheory.SepReal.FormalDegreeRatio.degRatio_holds | exact GlobalTheory.SepReal.FormalDegreeRatio.degRatio_holds | (intros; apply GlobalTheory.SepReal.FormalDegreeRatio.degRatio_holds <;> assumption)
end


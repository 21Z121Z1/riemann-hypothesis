import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
import Formalism.LocalToGlobal.CMDeterminantIdeals.Bundle0001
import Formalism.PolynomialDimension.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0861
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsPowPrincipalFractionalIdeal
import Formalism.PairingDivisors.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0498
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0858
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0513

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftingObstructionEqOfCohomologousCocycles
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBObs

theorem isObU_of_cob : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (u u' : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ) (t : ∀ T : C, (F.obj T)ˣ) (c : GlobalTheory.CatCoh.H2 (ext R₁ F)), L.IsFun → (∀ T T' a, (u' T T' a : F.obj T') * mp F a (t T : F.obj T) = (t T' : F.obj T') * (u T T' a : F.obj T')) → IsObU L α u c → IsObU L α u' c := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F L u u' t c hfun hrel hob
  obtain ⟨v, σ, z, hv, hσ, hc, hz⟩ := hob
  have hlift : ∀ T, ∃ τ : (L.B T)ˣ, L.p T (τ : L.B T) = (t T : F.obj T) := by
    intro T
    obtain ⟨b, hb⟩ := L.surj T (t T : F.obj T)
    obtain ⟨b', hb'⟩ := L.surj T (((t T)⁻¹ : (F.obj T)ˣ) : F.obj T)
    have hn : L.p T (b * b' - 1) = 0 := by
      rw [map_sub, map_mul, map_one, hb, hb']; simp
    rw [L.ker] at hn
    have hnil : IsNilpotent (b * b' - 1) := by
      refine ⟨2, ?_⟩
      have h2 : (b * b' - 1) ^ 2 ∈ (I.map (algebraMap R (L.B T))) ^ 2 := Ideal.pow_mem_pow hn 2
      rw [← Ideal.map_pow, hI, Ideal.zero_eq_bot, Ideal.map_bot] at h2
      simpa using h2
    have hu : IsUnit (b * b') := by simpa using hnil.isUnit_one_add
    exact ⟨(isUnit_of_mul_isUnit_left hu).unit, by simp [hb]⟩
  choose τ hτ using hlift
  let ρu : ∀ {T T' : C} (_ : T ⟶ T'), (L.B T)ˣ →* (L.B T')ˣ := fun a ↦ Units.map (L.ρ a).toRingHom.toMonoidHom
  refine ⟨fun T T' a ↦ τ T' * v T T' a * (ρu a (τ T))⁻¹, σ, z, ?_, hσ, hc, ?_⟩
  · intro T T' a
    have hm : IsUnit (mp F a (t T : F.obj T)) := (t T).isUnit.map (mp F a)
    have hinv : (((ρu a (τ T))⁻¹ : (L.B T')ˣ) : L.B T') * L.ρ a (τ T : L.B T) = 1 := by
      have := (ρu a (τ T)).inv_mul
      simpa [ρu] using this
    refine (hm.mul_left_inj).mp ?_
    have key : L.p T' (((ρu a (τ T))⁻¹ : (L.B T')ˣ) : L.B T') * L.p T' (L.ρ a (τ T : L.B T)) = 1 := by
      rw [← map_mul, hinv, map_one]
    rw [hrel, ← hτ T, ← L.nat a]
    simp only [Units.val_mul, map_mul]
    rw [_root_.mul_assoc _ (L.p T' _), key, _root_.mul_one, hτ T', hv]
  · intro T T' T'' a b
    refine ⟨(hz T T' T'' a b).1, ?_⟩
    have hzb := (hz T T' T'' a b).2
    have e1 : L.ρ b ((((ρu a (τ T))⁻¹ : (L.B T')ˣ) : L.B T')) * L.ρ b (L.ρ a (τ T : L.B T)) = 1 := by
      have h : (((ρu a (τ T))⁻¹ : (L.B T')ˣ) : L.B T') * L.ρ a (τ T : L.B T) = 1 := by
        simpa [ρu] using (ρu a (τ T)).inv_mul
      rw [← map_mul, h, map_one]
    have e2 : (((ρu b (τ T'))⁻¹ : (L.B T'')ˣ) : L.B T'') * L.ρ b (τ T' : L.B T') = 1 := by
      have := (ρu b (τ T')).inv_mul
      simpa [ρu] using this
    have e3 : (((ρu (a ≫ b) (τ T))⁻¹ : (L.B T'')ˣ) : L.B T'') * L.ρ b (L.ρ a (τ T : L.B T)) = 1 := by
      have := (ρu (a ≫ b) (τ T)).inv_mul
      rw [← hfun a b]
      simpa [ρu] using this
    have he : L.ρ b ((((ρu a (τ T))⁻¹ : (L.B T')ˣ) : L.B T')) = (((ρu (a ≫ b) (τ T))⁻¹ : (L.B T'')ˣ) : L.B T'') := by
      linear_combination (((ρu (a ≫ b) (τ T))⁻¹ : (L.B T'')ˣ) : L.B T'') * e1 - (L.ρ b ((((ρu a (τ T))⁻¹ : (L.B T')ˣ) : L.B T'))) * e3
    simp only [Units.val_mul, map_mul]
    rw [he]
    linear_combination ((τ T'' : L.B T'') * L.ρ b (v T T' a : L.B T') * (v T' T'' b : L.B T'') * (((ρu (a ≫ b) (τ T))⁻¹ : (L.B T'')ˣ) : L.B T'')) * e2 + ((τ T'' : L.B T'') * (((ρu (a ≫ b) (τ T))⁻¹ : (L.B T'')ˣ) : L.B T'')) * hzb

end GlobalTheory.LBObs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapMulScalar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitCentral

theorem exists_unitary {A : Type} [CommRing A] (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x)
    (e a b : A) (he : e * e = e) (hc : e * σ e = 0) (hab : a * b = 1) :
    ∃ u : A, u * σ u = 1 ∧ (e + σ e) * (u - 1) = u - 1 ∧ e * u = e * a := by
  have he' : σ e * σ e = σ e := by rw [← map_mul, he]
  have hab' : σ a * σ b = 1 := by rw [← map_mul, hab, map_one]
  refine ⟨e * a + σ e * σ b + (1 - e - σ e), ?_, ?_, ?_⟩
  · simp only [map_add, map_mul, map_sub, map_one, hσ]
    linear_combination (a * b - a - b + 1) * he + (σ a * σ b - σ a - σ b + 1) * he' +
      (a * σ a + b * σ b - a - b - σ a - σ b + 2) * hc + e * hab + σ e * hab'
  · linear_combination (a - 1) * he + (σ b - 1) * he' + (a + σ b - 2) * hc
  · linear_combination (a - 1) * he + (σ b - 1) * hc

theorem exists_scalar {A : Type} [CommRing A] (σ : A →+* A) {n : ℕ} (J : Matrix (Fin n) (Fin n) A)
    (u : A) (hu : u * σ u = 1) :
    ∃ z : Formalism.UG.UJ σ J, ((z : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = u • (1 : Matrix (Fin n) (Fin n) A) := by
  have hu' : σ u * u = 1 := by rw [mul_comm, hu]
  refine ⟨⟨⟨u • 1, σ u • 1, ?_, ?_⟩, ?_⟩, rfl⟩
  · simp [smul_smul, hu, hu']
  · simp [smul_smul, hu, hu']
  · show Formalism.UG.cT σ (u • (1 : Matrix (Fin n) (Fin n) A)) * J * (u • (1 : Matrix (Fin n) (Fin n) A)) = J
    have : Formalism.UG.cT σ (u • (1 : Matrix (Fin n) (Fin n) A)) = σ u • (1 : Matrix (Fin n) (Fin n) A) := by
      ext i j
      by_cases h : i = j
      · subst h; simp [Formalism.UG.cT]
      · simp [Formalism.UG.cT, Matrix.one_apply, h, Ne.symm h]
    rw [this]
    simp [smul_smul, hu, hu']

theorem supp_scalar {A : Type} [CommRing A] {n : ℕ} (f u : A) (h : f * (u - 1) = u - 1) (i j : Fin n) :
    f * (u • (1 : Matrix (Fin n) (Fin n) A) - 1) i j = (u • (1 : Matrix (Fin n) (Fin n) A) - 1) i j := by
  by_cases hij : i = j
  · subst hij; simpa using h
  · simp [hij]

theorem scalar_comm {A : Type} [CommRing A] {n : ℕ} (u : A) (M : Matrix (Fin n) (Fin n) A) :
    (u • (1 : Matrix (Fin n) (Fin n) A)) * M = M * (u • (1 : Matrix (Fin n) (Fin n) A)) := by
  simp

theorem map_mul_scalar {A R : Type} [CommRing A] [CommRing R] (φ : A →+* R) {n : ℕ} (u : A)
    (M : Matrix (Fin n) (Fin n) A) :
    (M * (u • (1 : Matrix (Fin n) (Fin n) A))).map φ = φ u • M.map φ := by
  ext i j
  simp

theorem cA_cA (D : D7) (x : Formalism.L2.Theta.AE D) : cA D (cA D x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    have : D.sp.cm.sig (D.sp.cm.sig b) = b := star_star b
    simp [cA, sigR, this]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem mulVec_shift {R : Type} [CommRing R] {n : ℕ} (B M : Matrix (Fin n) (Fin n) R) (e u p : R)
    (h : e * u = e * p) (c c' z y : Fin n → R) (hc : ∀ i, c' i = p * c i)
    (hy : (fun a => e * M.mulVec y a) = fun a => e * B.mulVec (fun i => c i * z i) a) :
    (fun a => e * (u • M).mulVec y a) = fun a => e * B.mulVec (fun i => c' i * z i) a := by
  funext a
  have h1 := congrFun hy a
  have h2 : (fun i => c' i * z i) = p • (fun i => c i * z i) := by
    funext i; simp [hc, mul_assoc]
  rw [h2, Matrix.mulVec_smul, Matrix.smul_mulVec]
  simp only [Pi.smul_apply, smul_eq_mul] at h1 ⊢
  linear_combination (M.mulVec y a) * h + p * h1

theorem hmul {D : D7} {V : HSp D} (g h : GA D V) :
    Formalism.L2.Theta.mt V (g * h) = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V h := by
  unfold Formalism.L2.Theta.mt
  rw [map_mul, Units.val_mul]

theorem hinj {D : D7} {V : HSp D} (g h : GA D V) (hh : Formalism.L2.Theta.mt V g = Formalism.L2.Theta.mt V h) :
    g = h := Subtype.ext (Units.ext hh)

theorem hfin {D : D7} {V : HSp D} (g : GA D V) :
    finMat D.sp.cm.sig V.gram g = (Formalism.L2.Theta.mt V g).map (finPart D) := rfl

theorem exists_mt {D : D7} (V : HSp D) (u : Formalism.L2.Theta.AE D) (hu : u * cA D u = 1) :
    ∃ ζ : GA D V, Formalism.L2.Theta.mt V ζ =
      u • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Theta.AE D)) :=
  exists_scalar (cA D) (JR (AF D.host.F) V.gram) u hu

theorem shift_pow {D : D7} (ϖ : D.host.E) (hϖ : ϖ ≠ 0) (d : List ℤ) (i : ℕ) (hi : i < d.length) :
    finPart D (incA D (ϖ ^ ((d.map (· + 1)).getD i 0))) =
      finPart D (incA D ϖ) * finPart D (incA D (ϖ ^ (d.getD i 0))) := by
  have : (d.map (· + 1)).getD i 0 = d.getD i 0 + 1 := by
    simp [List.getD_eq_getElem?_getD, hi]
  rw [this, zpow_add_one₀ hϖ, map_mul, map_mul, mul_comm]

theorem finMat_scalar {D : D7} {V : HSp D} (α ζ : GA D V) (u : Formalism.L2.Theta.AE D)
    (hmt : Formalism.L2.Theta.mt V ζ = u • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Theta.AE D))) :
    finMat D.sp.cm.sig V.gram (α * ζ : GA D V) = finPart D u • finMat D.sp.cm.sig V.gram α := by
  rw [hfin, hfin, hmul, hmt]
  exact map_mul_scalar _ _ _

theorem central : ∀ {D : D7} (V : HSp D) (e : Formalism.L2.Theta.AE D) (ϖ : D.host.E), IsSplitIdem D e → ϖ ≠ 0 → ∃ ζ : GA D V, SuppAt e V ζ ∧ (∀ g, Commute ζ g) ∧ ∀ (d : List ℤ) (α : GA D V), DivAt V e ϖ d α → DivAt V e ϖ (d.map (· + 1)) (α * ζ) := by
  intro D V e ϖ he hϖ
  obtain ⟨u, hu, hs, hue⟩ := exists_unitary (cA D) (cA_cA D) e (incA D ϖ) (incA D ϖ⁻¹) he.1 he.2.1
    (by rw [← map_mul, mul_inv_cancel₀ hϖ, map_one])
  obtain ⟨ζ, hmt⟩ : ∃ ζ : GA D V, Formalism.L2.Theta.mt V ζ =
      u • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Theta.AE D)) :=
    exists_mt V u hu
  refine ⟨ζ, ?_, ?_, ?_⟩
  · intro i j
    rw [hmt]
    exact supp_scalar _ _ hs i j
  · intro g
    refine hinj (ζ * g) (g * ζ) ?_
    rw [hmul, hmul, hmt]
    exact scalar_comm _ _
  · rintro d α ⟨hd, B, h1, h2, h3, h4⟩
    have hF := finMat_scalar α ζ u hmt
    have hup : finPart D e * finPart D u = finPart D e * finPart D (incA D ϖ) := by
      rw [← map_mul, hue, map_mul]
    have hc : ∀ i : Fin V.rank, finPart D (incA D (ϖ ^ ((d.map (· + 1)).getD i.1 0))) =
        finPart D (incA D ϖ) * finPart D (incA D (ϖ ^ (d.getD i.1 0))) :=
      fun i => shift_pow ϖ hϖ d i.1 (lt_of_lt_of_eq i.2 hd.symm)
    refine ⟨by simpa using hd, B, h1, h2, ?_, ?_⟩
    · intro y hy
      obtain ⟨z, hz, hyz⟩ := h3 y hy
      refine ⟨z, hz, ?_⟩
      rw [hF]
      exact mulVec_shift B _ _ _ _ hup _ _ z y hc hyz
    · intro z hz
      obtain ⟨y, hy, hyz⟩ := h4 z hz
      refine ⟨y, hy, ?_⟩
      rw [hF]
      exact mulVec_shift B _ _ _ _ hup _ _ z y hc hyz

end GlobalTheory.SplitCentral
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatCharPowEqDetPow
section
noncomputable section

namespace GlobalTheory.DefPt

open Matrix

section Char

variable {K : Type} [Field K] {n : ℕ} (χ : Matrix (Fin n) (Fin n) K →* K)

theorem matChar_submatrix (σ : Equiv.Perm (Fin n)) (M : Matrix (Fin n) (Fin n) K) :
    χ (M.submatrix σ σ) = χ M := by
  have h1 : ∀ N : Matrix (Fin n) (Fin n) K,
      σ.toPEquiv.toMatrix * N * σ.symm.toPEquiv.toMatrix = N.submatrix σ σ := by
    intro N
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Equiv.symm_symm, submatrix_submatrix]
    rfl
  have h2 := congrArg χ (h1 1)
  rw [submatrix_one_equiv, Matrix.mul_one, map_mul, map_one] at h2
  rw [← h1 M, map_mul, map_mul, mul_comm (χ _) (χ M), mul_assoc, h2, mul_one]

theorem matChar_transvection [CharZero K] {i j : Fin n} (hij : i ≠ j) (c : K) :
    χ (transvection i j c) = 1 := by
  set D : Matrix (Fin n) (Fin n) K := diagonal (Function.update 1 i 2)
  set D' : Matrix (Fin n) (Fin n) K := diagonal (Function.update 1 i (1 / 2))
  have hDD : D * D' = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [Function.update_of_ne hk]
  have hD : χ D ≠ 0 := fun h => by
    have := congrArg χ hDD
    rw [map_mul, map_one, h, zero_mul] at this
    exact zero_ne_one this
  have hT : χ (transvection i j c) ≠ 0 := fun h => by
    have := congrArg χ (transvection_mul_transvection_same i j hij c (-c))
    rw [add_neg_cancel, transvection_zero, map_mul, map_one, h, zero_mul] at this
    exact zero_ne_one this
  have hcomm : D * transvection i j c = transvection i j (c + c) * D := by
    ext a b
    rw [diagonal_mul, mul_diagonal]
    have hdi : Function.update (1 : Fin n → K) i 2 i = 2 := by simp
    have hdj : Function.update (1 : Fin n → K) i 2 j = 1 := by simp [Ne.symm hij]
    simp only [transvection, Matrix.add_apply, Matrix.single_apply]
    by_cases h : a = i ∧ b = j
    · obtain ⟨rfl, rfl⟩ := h
      rw [Matrix.one_apply_ne hij, hdi, hdj]
      simp only [and_self, ite_true]
      ring
    · have h' : ¬(i = a ∧ j = b) := fun h' => h ⟨h'.1.symm, h'.2.symm⟩
      rw [if_neg h', if_neg h']
      simp only [add_zero]
      by_cases hab : a = b
      · subst hab; ring
      · rw [Matrix.one_apply_ne hab]; ring
  have e := congrArg χ hcomm
  rw [map_mul, map_mul, ← transvection_mul_transvection_same i j hij, map_mul, mul_comm (χ D)] at e
  have e2 : χ (transvection i j c) * 1 = χ (transvection i j c) * χ (transvection i j c) := by
    rw [mul_one]
    exact mul_right_cancel₀ hD e
  exact (mul_left_cancel₀ hT e2).symm

theorem matChar_mulSingle (k k' : Fin n) (a : K) :
    χ (diagonal (Pi.mulSingle k a)) = χ (diagonal (Pi.mulSingle k' a)) := by
  rw [← matChar_submatrix χ (Equiv.swap k k') (diagonal (Pi.mulSingle k' a)), submatrix_diagonal_equiv]
  congr 2
  funext x
  simp only [Function.comp_apply, Pi.mulSingle_apply]
  by_cases hx : x = k
  · subst hx; simp
  · by_cases hx' : x = k'
    · subst hx'; rw [Equiv.swap_apply_right]; simp [hx, Ne.symm hx]
    · rw [Equiv.swap_apply_of_ne_of_ne hx hx']; simp [hx, hx']

theorem matChar_diagonal_pow (m : ℕ) (hs : ∀ t : K, χ (t • 1) = t ^ m) (d : Fin n → K) :
    χ (diagonal d) ^ n = (diagonal d).det ^ m := by
  let ψ : (Fin n → K) →* K := χ.comp (diagonalRingHom (Fin n) K).toMonoidHom
  have hψ : ∀ v, ψ v = χ (diagonal v) := fun v => rfl
  have hone : ∀ (k : Fin n) (a : K), χ (diagonal (Pi.mulSingle k a)) ^ n = a ^ m := by
    intro k a
    calc χ (diagonal (Pi.mulSingle k a)) ^ n = ∏ k' : Fin n, ψ (Pi.mulSingle k' a) := by
          rw [Finset.prod_congr rfl fun k' _ => (hψ _).trans (matChar_mulSingle χ k' k a), Finset.prod_const,
            Finset.card_univ, Fintype.card_fin]
      _ = ψ (fun _ => a) := by rw [← map_prod, Finset.univ_prod_mulSingle]
      _ = a ^ m := by rw [hψ, ← smul_one_eq_diagonal, hs]
  calc χ (diagonal d) ^ n = (∏ k, ψ (Pi.mulSingle k (d k))) ^ n := by
        rw [← map_prod, Finset.univ_prod_mulSingle, hψ]
    _ = ∏ k, d k ^ m := by
        rw [← Finset.prod_pow]; exact Finset.prod_congr rfl fun k _ => hone k (d k)
    _ = (diagonal d).det ^ m := by rw [det_diagonal, Finset.prod_pow]

theorem matChar_pow_eq_det_pow [CharZero K] (m : ℕ) (hs : ∀ t : K, χ (t • 1) = t ^ m)
    (g : Matrix (Fin n) (Fin n) K) : χ g ^ n = g.det ^ m := by
  refine diagonal_transvection_induction (fun M => χ M ^ n = M.det ^ m) g
    (fun D _ => matChar_diagonal_pow χ m hs D) (fun t => ?_) (fun A B hA hB => ?_)
  · show χ t.toMatrix ^ n = t.toMatrix.det ^ m
    rw [show t.toMatrix = transvection t.i t.j t.c from rfl, matChar_transvection χ t.hij,
      det_transvection_of_ne _ _ t.hij]
    simp
  · show χ (A * B) ^ n = (A * B).det ^ m
    have hA' : χ A ^ n = A.det ^ m := hA
    have hB' : χ B ^ n = B.det ^ m := hB
    rw [map_mul, det_mul, mul_pow, mul_pow, hA', hB']

end Char

end GlobalTheory.DefPt

namespace GlobalTheory.DefPt

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine MvPolynomial
open scoped Matrix

def rhoDetHom {n : ℕ} (la : Fin n → ℕ) (K : Type) [Field K] [CharZero K] : Matrix (Fin n) (Fin n) K →* K where
  toFun g := (GlobalTheory.DefPt.rhoMat la g).det
  map_one' := by rw [Model.rhoMat_one, Matrix.det_one]
  map_mul' g h := by rw [Model.rhoMat_mul, Matrix.det_mul, mul_comm]

theorem det_rhoMat_pow : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (la : Fin n → ℕ), Antitone la →
    ∀ g : Matrix (Fin n) (Fin n) K, (rhoMat la g).det ^ n = g.det ^ (size la * dim la) := by
  intro K _ _ n la _ g
  have hs : ∀ t : K, rhoDetHom la K (t • 1) = t ^ (size la * dim la) := by
    intro t
    show (GlobalTheory.DefPt.rhoMat la (t • 1)).det = _
    rw [Model.rhoMat_scalar, Matrix.det_smul, Matrix.det_one, mul_one, dim_eq_card, pow_mul]
  exact matChar_pow_eq_det_pow (rhoDetHom la K) _ hs g

end GlobalTheory.DefPt

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial in
open scoped Matrix in
example : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (la : Fin n → ℕ), Antitone la → ∀ g : Matrix (Fin n) (Fin n) K, (rhoMat la g).det ^ n = g.det ^ (size la * dim la) :=
  GlobalTheory.DefPt.det_rhoMat_pow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanLogMetricGeneratorEqMeanPeriod
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.MeanPeriodGenerator

theorem ellT_eq_span (D : D7) (cD : D.what₂.Tau → ℂ) (h : IsDgen D cD)
    (M : IntermediateField ℚ ℂ) [NumberField M] (hM : ∀ τ x, TaylorLogMetric.embT D τ x ∈ M)
    (τ : D.what₂.Tau) (hc : cD τ ∈ M) :
    TaylorLogMetric.ellT D M τ = Submodule.span (𝓞 M) {(⟨cD τ, hc⟩ : M)} := by
  obtain ⟨M₀, _, hM₀, hs⟩ := h
  obtain ⟨s, hsc, hs⟩ := hs τ
  have hs0 : s ≠ 0 := GlobalTheory.Glob.ne_zero_of_span_eq hM₀ hs.symm
  have hc0 : cD τ ≠ 0 := fun h => hs0 (Subtype.ext (hsc.trans h))
  haveI : NumberField (M ⊔ M₀ : IntermediateField ℚ ℂ) := NumberField.mk
  have hM' : ∀ τ x, TaylorLogMetric.embT D τ x ∈ (M ⊔ M₀ : IntermediateField ℚ ℂ) :=
    fun τ x => (le_sup_left : M ≤ M ⊔ M₀) (hM τ x)
  have h' := GlobalTheory.EigenlineBaseChange.ellT_eq_span_of_le D M₀ (M ⊔ M₀) le_sup_right hM₀ τ s hs
  apply le_antisymm
  · intro x hx
    have hx' : (⟨(x : ℂ), (le_sup_left : M ≤ M ⊔ M₀) x.2⟩ : (M ⊔ M₀ : IntermediateField ℚ ℂ)) ∈
        TaylorLogMetric.ellT D (M ⊔ M₀) τ := by
      rw [GlobalTheory.Glob.mem_ellT_iff hM']
      exact (GlobalTheory.Glob.mem_ellT_iff hM τ x).1 hx
    rw [h', Submodule.mem_span_singleton] at hx'
    obtain ⟨c, hcx⟩ := hx'
    have e : ((c : (M ⊔ M₀ : IntermediateField ℚ ℂ)) : ℂ) * (s : ℂ) = (x : ℂ) :=
      congrArg (fun a : (M ⊔ M₀ : IntermediateField ℚ ℂ) => (a : ℂ)) hcx
    have hi : IsIntegral ℤ ((c : (M ⊔ M₀ : IntermediateField ℚ ℂ)) : ℂ) :=
      (GlobalTheory.EigenlineBaseChange.isIntegral_coe_iff _).2 c.isIntegral_coe
    have e2 : ((c : (M ⊔ M₀ : IntermediateField ℚ ℂ)) : ℂ) = (x : ℂ) * (cD τ)⁻¹ := by
      rw [← e, hsc, mul_inv_cancel_right₀ hc0]
    rw [e2] at hi
    rw [Submodule.mem_span_singleton]
    refine ⟨⟨x * (⟨cD τ, hc⟩ : M)⁻¹, (GlobalTheory.EigenlineBaseChange.isIntegral_coe_iff _).1 hi⟩, ?_⟩
    exact inv_mul_cancel_right₀ (fun h => hc0 (congrArg (fun a : M => (a : ℂ)) h)) x
  · rw [Submodule.span_singleton_le_iff_mem, GlobalTheory.Glob.mem_ellT_iff hM]
    have := (GlobalTheory.Glob.mem_ellT_iff hM₀ τ s).1 (hs ▸ Submodule.mem_span_singleton_self s)
    rw [hsc] at this
    exact this

theorem mean_logMet_eq : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (cD : D.what₂.Tau → ℂ), StandardLatticesGL3.Crv D cc dl → GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.MeanPeriodAt D cc dl → IsDgen D cD → (∀ τ, cD τ ≠ 0) ∧ ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M], TaylorLogMetric.DataIn D (TaylorLogMetric.tor0 D cc dl) M → (∀ τ, cD τ ∈ M) → ∀ τ, (∑ ρ : M →ₐ[ℚ] ℂ, -TaylorLogMetric.logMet M (TaylorLogMetric.lamOf D cc dl) ρ (TaylorLogMetric.liftM M (cD τ))) / (Module.finrank ℚ M : ℝ) = TaylorLogMetric.logOmVal D := by
  intro D cc dl cD hc hmean hgen
  have hne : ∀ τ, cD τ ≠ 0 := by
    intro τ h
    obtain ⟨M₀, _, hM₀, hs⟩ := hgen
    obtain ⟨s, hsc, hs⟩ := hs τ
    exact GlobalTheory.Glob.ne_zero_of_span_eq hM₀ hs.symm (Subtype.ext (hsc.trans h))
  refine ⟨hne, fun M _ hD hcM τ => ?_⟩
  haveI : NumberField M := NumberField.mk
  have hell := ellT_eq_span D cD hgen M hD.1 τ (hcM τ)
  have hl : TaylorLogMetric.liftM M (cD τ) = ⟨cD τ, hcM τ⟩ := dif_pos (hcM τ)
  rw [hl, ← hmean M hD τ, Finset.sum_neg_distrib]
  exact (GlobalTheory.Glob.meanLogOm_eq_of_gen hD.1 (GlobalTheory.Glob.area_lamConj_pos hc hD) hell.symm).symm

end GlobalTheory.MeanPeriodGenerator
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedOrderOfLocalCongruenceSplit
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler

namespace GlobalTheory.CMVal.Euler.HatLoc

variable {E : Type} [Field E] [NumberField E]

theorem finMult {R : Type} [CommRing R] [IsDedekindDomain R] {c : Ideal R} (hc : c ≠ ⊥) (v : HeightOneSpectrum R) :
    FiniteMultiplicity v.asIdeal c :=
  FiniteMultiplicity.of_prime_left v.prime hc

omit [NumberField E] in
theorem expIn_eq_zero {c : Ideal (OF E)} {v : HeightOneSpectrum (OF E)} (h : ¬ v.asIdeal ∣ c) : expIn c v = 0 :=
  multiplicity_eq_zero.2 h

theorem exists_global {c : Ideal (OF E)} (hc : c ≠ ⊥) {z : Af E} (hz : ∀ v, LocIn (expIn c v) v z) :
    ∃ a : OF E, ∀ P : HeightOneSpectrum (𝓞 E),
      Valued.v (z P - iota a P) ≤ WithZero.exp (-(expIn c (P.under (OF E)) : ℤ)) := by
  classical
  choose b hb using hz
  have hfin := Ideal.finite_factors (R := OF E) hc
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := hfin.toFinset) (fun v => v.asIdeal) (expIn c)
    (fun v _ => v.prime) (fun v _ w _ h h' => h (HeightOneSpectrum.ext h')) (fun v => b v)
  refine ⟨a, fun P => ?_⟩
  have h1 : a - b (P.under (OF E)) ∈ (P.under (OF E)).asIdeal ^ expIn c (P.under (OF E)) := by
    by_cases h : (P.under (OF E)).asIdeal ∣ c
    · exact ha _ (hfin.mem_toFinset.2 h)
    · simp [expIn_eq_zero h]
  have h2 := val_iota_le_of_mem (over_under P) _ h1
  have h3 : z P - iota a P = (z P - iota (b (P.under (OF E))) P) - iota (a - b (P.under (OF E))) P := by
    rw [iota_sub, sub_coord]; ring
  rw [h3]
  exact Valuation.map_sub_le _ (hb _ P (over_under P)) h2

theorem multiplicity_map_le [IsCMField E] {c : Ideal (OF E)} (hc : c ≠ ⊥)
    (hs : ∀ v : HeightOneSpectrum (OF E), v.asIdeal ∣ c → Splits v) (P : HeightOneSpectrum (𝓞 E)) :
    multiplicity P.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) ≤ expIn c (P.under (OF E)) := by
  set k := multiplicity P.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) with hk
  have h1 : Ideal.map (algebraMap (OF E) (𝓞 E)) c ≤ P.asIdeal ^ k := Ideal.le_of_dvd (pow_multiplicity_dvd _ _)
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · rw [h0]; exact Nat.zero_le _
  have h2 : (P.under (OF E)).asIdeal ∣ c :=
    Ideal.dvd_iff_le.2 (Ideal.map_le_iff_le_comap.1 (h1.trans (Ideal.pow_le_self hpos.ne')))
  refine (finMult hc _).le_multiplicity_of_pow_dvd (Ideal.dvd_iff_le.2 fun a ha => ?_)
  exact (((GlobalTheory.CMVal.Euler.SplitPlace.split_place E _ (hs _ h2)).2 P (over_under P)).2.1 a k).1 (h1 (Ideal.mem_map_of_mem _ ha))

theorem mem_hatO_of_locIn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ →
    (∀ v : HeightOneSpectrum (OF E), v.asIdeal ∣ c → Splits v) → ∀ z : Af E, (∀ v, LocIn (expIn c v) v z) →
      z ∈ hatO c := by
  intro E _ _ _ c hc hs z hz
  obtain ⟨a, ha⟩ := exists_global hc hz
  have hN : 0 < Ideal.absNorm c := Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  obtain ⟨x, y, hy, hxy⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat E _ hN).2 z
    (fun P => (hz _).val_le (over_under P))
  have hny : Ideal.absNorm c • y = iota ((Ideal.absNorm c : ℕ) : OF E) * y := by
    rw [nsmul_eq_mul, iota, map_natCast, map_natCast]
  rw [hny] at hxy
  have hc' : Ideal.map (algebraMap (OF E) (𝓞 E)) c ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hc
  have hx : x - algebraMap (OF E) (𝓞 E) a ∈ Ideal.map (algebraMap (OF E) (𝓞 E)) c := by
    rw [← Ideal.iInf_maxPowDividing_eq hc', Ideal.mem_iInf]
    intro P
    rw [HeightOneSpectrum.maxPowDividing_eq_pow_multiplicity hc']
    refine Ideal.pow_le_pow_right (multiplicity_map_le hc hs P) ?_
    rw [← P.intValuation_le_pow_iff_mem, ← HeightOneSpectrum.valuation_of_algebraMap (K := E),
      ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← FiniteAdeleRing.algebraMap_apply]
    have h1 : algebraMap E (Af E) (algebraMap (𝓞 E) E (x - algebraMap (OF E) (𝓞 E) a)) =
        (z - iota a) - iota ((Ideal.absNorm c : ℕ) : OF E) * y := by
      rw [map_sub, map_sub, hxy]
      change algebraMap E (Af E) (x : E) - iota a = _
      ring
    rw [h1, sub_coord, sub_coord, mul_coord]
    refine Valuation.map_sub_le _ (ha P) ?_
    rw [map_mul]
    exact (mul_le_mul' (val_iota_le_of_mem (over_under P) _
      (Ideal.le_of_dvd (pow_multiplicity_dvd _ _) (Ideal.absNorm_mem c))) (hy P)).trans_eq (mul_one _)
  rw [hxy]
  refine add_mem (algebraMap_mem_hatO (mem_orderC.2 ⟨a, _, hx, ?_⟩)) (PicFin.mul_mem_hatO (Ideal.absNorm_mem c) hy)
  rw [map_sub]
  change (x : E) = algebraMap (OF E) E a + ((x : E) - algebraMap (OF E) E a)
  ring

end GlobalTheory.CMVal.Euler.HatLoc
end
end


import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1703
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1089
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1090
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureTensorOInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0108
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0323
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1680
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1690
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0027
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EncardSmulMemLeEncardSmulInterNonempty

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryAdelicPointPrescribedFrameImages
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.SphEis.ColImg

open Formalism.UG (cT_mul cT_one)

section Ring

variable {S : Type} [CommRing S] (s : S →+* S)

theorem cT_add' {a b : Type} (M N : Matrix a b S) : cT s (M + N) = cT s M + cT s N := by
  ext i k; simp [cT]

theorem cT_zero' {a b : Type} : cT s (0 : Matrix a b S) = 0 := by
  ext i k; simp [cT]

theorem cT_cT' (hs : ∀ x, s (s x) = x) {a b : Type} (M : Matrix a b S) : cT s (cT s M) = M := by
  ext i k; simp [cT, hs]

theorem cT_gram {n a b : ℕ} (hs : ∀ x, s (s x) = x) (J : Matrix (Fin n) (Fin n) S) (hJ : cT s J = J)
    (M : Matrix (Fin n) (Fin a) S) (N : Matrix (Fin n) (Fin b) S) :
    cT s (cT s M * J * N) = cT s N * J * M := by
  rw [cT_mul, cT_mul, cT_cT' s hs, hJ, Matrix.mul_assoc]

theorem gram_comb {n j m : ℕ} (J : Matrix (Fin n) (Fin n) S) (J0 : Matrix (Fin m) (Fin m) S)
    (A B : Matrix (Fin n) (Fin j) S) (Z : Matrix (Fin n) (Fin m) S)
    (pX pY : Matrix (Fin j) (Fin n) S) (p0 : Matrix (Fin m) (Fin n) S)
    (aa : cT s A * J * A = 0) (bb : cT s B * J * B = 0) (ab : cT s A * J * B = 1) (ba : cT s B * J * A = 1)
    (az : cT s A * J * Z = 0) (bz : cT s B * J * Z = 0) (za : cT s Z * J * A = 0) (zb : cT s Z * J * B = 0)
    (zz : cT s Z * J * Z = J0) :
    cT s (A * pX + Z * p0 + B * pY) * J * (A * pX + Z * p0 + B * pY) =
      cT s pX * pY + cT s p0 * J0 * p0 + cT s pY * pX := by
  have h1 : cT s A * (J * (A * pX + Z * p0 + B * pY)) = pY := by
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, aa, az, ab, Matrix.zero_mul, Matrix.one_mul, zero_add]
  have h2 : cT s Z * (J * (A * pX + Z * p0 + B * pY)) = J0 * p0 := by
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, za, zz, zb, Matrix.zero_mul, zero_add, add_zero]
  have h3 : cT s B * (J * (A * pX + Z * p0 + B * pY)) = pX := by
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, ba, bz, bb, Matrix.zero_mul, Matrix.one_mul, zero_add, add_zero]
  rw [cT_add', cT_add', cT_mul, cT_mul, cT_mul]
  simp only [Matrix.add_mul, Matrix.mul_assoc, h1, h2, h3]

end Ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sig_invol {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem sigR_invol (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (e : AF F ⊗[F] E) :
    sigR (AF F) σ (sigR (AF F) σ e) = e := by
  induction e using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a x => simp [sigR, hσ]

theorem cT_adMat (σ : E →ₐ[F] E) {a b : Type} (X : Matrix a b E) :
    cT (sigR (AF F) σ) (adMat F X) = adMat F (cT (σ : E →+* E) X) := by
  ext i k; simp [cT, adMat, sigR, inclR]

end GlobalTheory.SphEis.ColImg

namespace GlobalTheory.SphEis.ColImg

open Formalism.UG (cT_mul cT_one)

section Ring

variable {S : Type} [CommRing S] (s : S →+* S)

theorem images_ring {n j m : ℕ} (Ja Jai : Matrix (Fin n) (Fin n) S) (j0 k0 : Matrix (Fin m) (Fin m) S)
    (hJi : Jai * Ja = 1) (hk0 : k0 * j0 = 1)
    (c d C' D' : Matrix (Fin n) (Fin j) S) (z Z' : Matrix (Fin n) (Fin m) S)
    (cc : cT s c * Ja * c = 0) (dd : cT s d * Ja * d = 0) (cd : cT s c * Ja * d = 1) (dc : cT s d * Ja * c = 1)
    (cz : cT s c * Ja * z = 0) (dz : cT s d * Ja * z = 0) (zc : cT s z * Ja * c = 0) (zd : cT s z * Ja * d = 0)
    (zz : cT s z * Ja * z = j0)
    (sum : c * (cT s d * Ja) + z * (k0 * (cT s z * Ja)) + d * (cT s c * Ja) = 1)
    (cc' : cT s C' * Ja * C' = 0) (dd' : cT s D' * Ja * D' = 0) (cd' : cT s C' * Ja * D' = 1) (dc' : cT s D' * Ja * C' = 1)
    (cz' : cT s C' * Ja * Z' = 0) (dz' : cT s D' * Ja * Z' = 0) (zc' : cT s Z' * Ja * C' = 0) (zd' : cT s Z' * Ja * D' = 0)
    (zz' : cT s Z' * Ja * Z' = j0) :
    ∃ u : GL (Fin n) S, cT s u.1 * Ja * u.1 = Ja ∧ u.1 * c = C' ∧ u.1 * z = Z' ∧ u.1 * d = D' := by
  obtain ⟨pX, hpX⟩ : ∃ p, p = cT s d * Ja := ⟨_, rfl⟩
  obtain ⟨p0, hp0⟩ : ∃ p, p = k0 * (cT s z * Ja) := ⟨_, rfl⟩
  obtain ⟨pY, hpY⟩ : ∃ p, p = cT s c * Ja := ⟨_, rfl⟩
  rw [← hpX, ← hp0, ← hpY] at sum
  have Xc : pX * c = 1 := by rw [hpX, dc]
  have Xz : pX * z = 0 := by rw [hpX, dz]
  have Xd : pX * d = 0 := by rw [hpX, dd]
  have Yc : pY * c = 0 := by rw [hpY, cc]
  have Yz : pY * z = 0 := by rw [hpY, cz]
  have Yd : pY * d = 1 := by rw [hpY, cd]
  have Oc : p0 * c = 0 := by rw [hp0, Matrix.mul_assoc, zc, Matrix.mul_zero]
  have Oz : p0 * z = 1 := by rw [hp0, Matrix.mul_assoc, zz, hk0]
  have Od : p0 * d = 0 := by rw [hp0, Matrix.mul_assoc, zd, Matrix.mul_zero]
  obtain ⟨g, hg⟩ : ∃ g, g = C' * pX + Z' * p0 + D' * pY := ⟨_, rfl⟩
  have gram : cT s g * Ja * g = Ja := by
    rw [hg, gram_comb s Ja j0 C' D' Z' pX pY p0 cc' dd' cd' dc' cz' dz' zc' zd' zz',
      ← gram_comb s Ja j0 c d z pX pY p0 cc dd cd dc cz dz zc zd zz, sum, cT_one, Matrix.one_mul, Matrix.mul_one]
  have hl : (Jai * cT s g * Ja) * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT s g), gram, hJi]
  have hr : g * (Jai * cT s g * Ja) = 1 := mul_eq_one_comm.1 hl
  refine ⟨⟨g, Jai * cT s g * Ja, hr, hl⟩, gram, ?_, ?_, ?_⟩
  · change g * c = C'
    simp only [hg, Matrix.add_mul, Matrix.mul_assoc, Xc, Oc, Yc, Matrix.mul_zero, Matrix.mul_one, add_zero]
  · change g * z = Z'
    simp only [hg, Matrix.add_mul, Matrix.mul_assoc, Xz, Oz, Yz, Matrix.mul_zero, Matrix.mul_one, add_zero, zero_add]
  · change g * d = D'
    simp only [hg, Matrix.add_mul, Matrix.mul_assoc, Xd, Od, Yd, Matrix.mul_zero, Matrix.mul_one, add_zero, zero_add]

end Ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem adMat_gram (σ : E →ₐ[F] E) {n a b : ℕ} (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin a) E)
    (Y : Matrix (Fin n) (Fin b) E) (R : Matrix (Fin a) (Fin b) E) (h : cT (σ : E →+* E) X * J * Y = R) :
    cT (sigR (AF F) σ) (adMat F X) * adMat F J * adMat F Y = adMat F R := by
  rw [cT_adMat, adMat, adMat, adMat, adMat, ← Matrix.map_mul, ← Matrix.map_mul, h]

theorem adMat_zero' {a b : Type} : adMat F (0 : Matrix a b E) = 0 := Matrix.map_zero _ (map_zero _)

theorem adMat_one' {a : Type} [DecidableEq a] : adMat F (1 : Matrix a a E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

theorem adMat_mul' {a b c : Type} [Fintype b] (X : Matrix a b E) (Y : Matrix b c E) :
    adMat F (X * Y) = adMat F X * adMat F Y := Matrix.map_mul

end GlobalTheory.SphEis.ColImg

namespace GlobalTheory.SphEis.ColImg

open Formalism.UG (cT_mul cT_one)

theorem exists_point_images :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ (C' D' : Matrix (Fin n) (Fin j) (AF F ⊗[F] E)) (Z' : Matrix (Fin n) (Fin m) (AF F ⊗[F] E)), cT (sigR (AF F) σ) C' * adMat F J * C' = 0 → cT (sigR (AF F) σ) D' * adMat F J * D' = 0 → cT (sigR (AF F) σ) C' * adMat F J * D' = 1 → cT (sigR (AF F) σ) C' * adMat F J * Z' = 0 → cT (sigR (AF F) σ) D' * adMat F J * Z' = 0 → cT (sigR (AF F) σ) Z' * adMat F J * Z' = adMat F J₀ → ∃ g : GAd σ J, (matHom _ σ J g).1 * adMat F C = C' ∧ (matHom _ σ J g).1 * adMat F Z = Z' ∧ (matHom _ σ J g).1 * adMat F D = D' := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ fr C' D' Z' cc dd cd cz dz zz
  have hσ : ∀ x, σ (σ x) = x := sig_invol fr.cm
  have hs : ∀ x, sigR (AF F) σ (sigR (AF F) σ x) = x := sigR_invol σ hσ
  have hJ : cT (sigR (AF F) σ) (adMat F J) = adMat F J := by rw [cT_adMat, cT_form fr.herm]
  have dc : cT (sigR (AF F) σ) D' * adMat F J * C' = 1 := by
    rw [← cT_gram _ hs _ hJ, cd, cT_one]
  have zc : cT (sigR (AF F) σ) Z' * adMat F J * C' = 0 := by rw [← cT_gram _ hs _ hJ, cz, cT_zero']
  have zd : cT (sigR (AF F) σ) Z' * adMat F J * D' = 0 := by rw [← cT_gram _ hs _ hJ, dz, cT_zero']
  have acc := adMat_gram (F := F) σ J C C 0 fr.cc
  have add := adMat_gram (F := F) σ J D D 0 fr.dd
  have acd := adMat_gram (F := F) σ J C D 1 fr.cd
  have adc := adMat_gram (F := F) σ J D C 1 fr.dc
  have acz := adMat_gram (F := F) σ J C Z 0 fr.cz
  have adz := adMat_gram (F := F) σ J D Z 0 fr.dz
  have azc := adMat_gram (F := F) σ J Z C 0 fr.zc
  have azd := adMat_gram (F := F) σ J Z D 0 fr.zd
  have azz := adMat_gram (F := F) σ J Z Z J₀ fr.zz
  rw [adMat_zero'] at acc add acz adz azc azd
  rw [adMat_one'] at acd adc
  have hJ0 : adMat F J₀⁻¹ * adMat F J₀ = 1 := by
    rw [← adMat_mul', Matrix.nonsing_inv_mul _ (det_isUnit fr.herm₀), adMat_one']
  have hJi : adMat F J⁻¹ * adMat F J = 1 := by
    rw [← adMat_mul', Matrix.nonsing_inv_mul _ (det_isUnit fr.herm), adMat_one']
  have hsum : adMat F C * (cT (sigR (AF F) σ) (adMat F D) * adMat F J) +
      adMat F Z * (adMat F J₀⁻¹ * (cT (sigR (AF F) σ) (adMat F Z) * adMat F J)) +
      adMat F D * (cT (sigR (AF F) σ) (adMat F C) * adMat F J) = 1 := by
    have := congrArg (adMat F) fr.sum
    rw [adMat_one'] at this
    rw [← this, cT_adMat, cT_adMat, cT_adMat]
    simp only [adMat_mul', adMat, Matrix.map_add _ (map_add _)]
  obtain ⟨u, hu, h1, h2, h3⟩ := images_ring (sigR (AF F) σ) (adMat F J) (adMat F J⁻¹) (adMat F J₀) (adMat F J₀⁻¹) hJi hJ0
    (adMat F C) (adMat F D) C' D' (adMat F Z) Z' acc add acd adc acz adz azc azd azz hsum cc dd cd dc cz dz zc zd zz
  exact ⟨(show HA (AF F) σ J from (⟨u, hu⟩ : HR (AF F) σ J)), h1, h2, h3⟩

end GlobalTheory.SphEis.ColImg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtensionOfLowSmoothLines
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.IoExtPf

section Rep

open Formalism.MainNotions.S

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool} {lam : Fin n → ℝ}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem exists_ext_mem (hU : IsURepOn (UJset ε) σ) {Λ : Fin n → ℝ} {S : Submodule ℂ H} (hS : IsKTypeOf ε σ Λ S) :
    ∃ w ∈ S, ‖w‖ = 1 ∧ IsWtOn (Formalism.REAL.Kset ε) σ (fun a => Λ (revNeg ε a)) w := by
  obtain ⟨v, hvS, hv0, hv⟩ := hS.2.2.2.1
  have hK := pM_mem (revNeg ε) (eps_revNeg ε)
  have hn : ‖σ (pM (revNeg ε)) v‖ = ‖v‖ := hU.2.1 _ (kset_uj hK) v
  have hp : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv0
  refine ⟨((‖v‖⁻¹ : ℝ) : ℂ) • σ (pM (revNeg ε)) v, ?_, ?_, isWtOn_smul (isWtOn_perm hU _ (eps_revNeg ε) hv) _⟩
  · exact Submodule.smul_mem _ _ (hS.2.1 _ hK v hvS)
  · rw [norm_smul, hn, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hp]

theorem lowK_irred (hσ : IsDS ε lam σ)
    (hl : ∀ w w' : H, ‖w‖ = 1 → w ∈ lowKSub ε lam σ →
      IsWtOn (Formalism.REAL.Kset ε) σ (fun a => Formalism.QuantumDeterminants.lowK ε lam (revNeg ε a)) w → ‖w'‖ = 1 → w' ∈ lowKSub ε lam σ →
      IsWtOn (Formalism.REAL.Kset ε) σ (fun a => Formalism.QuantumDeterminants.lowK ε lam (revNeg ε a)) w' → ∃ c : ℂ, w' = c • w)
    (N : Submodule ℂ H) (hN : N ≤ lowKSub ε lam σ) (hst : IsKStableOn ε σ N) : N = ⊥ ∨ N = lowKSub ε lam σ := by
  obtain ⟨-, -, hU, -, -, ⟨S, hS⟩, -⟩ := hσ
  have hle : ∀ S', IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S' → S' ≤ lowKSub ε lam σ := fun S' h =>
    le_sSup (s := {S | IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S}) h
  have key : lowKSub ε lam σ = S := by
    refine le_antisymm (sSup_le fun S' hS' => ?_) (hle S hS)
    obtain ⟨w, hw, hw1, hwt⟩ := exists_ext_mem hU hS
    obtain ⟨w', hw', hw1', hwt'⟩ := exists_ext_mem hU hS'
    obtain ⟨c, hc⟩ := hl w w' hw1 (hle S hS hw) hwt hw1' (hle S' hS' hw') hwt'
    have hm : w' ∈ S' ⊓ S := ⟨hw', hc ▸ S.smul_mem c hw⟩
    rcases hS'.2.2.1 (S' ⊓ S) inf_le_left (fun g hg v hv => ⟨hS'.2.1 g hg v hv.1, hS.2.1 g hg v hv.2⟩) with h | h
    · rw [h, Submodule.mem_bot] at hm
      rw [hm, norm_zero] at hw1'
      exact absurd hw1' zero_ne_one
    · exact h ▸ inf_le_right
  rw [key] at hN ⊢
  exact hS.2.2.1 N hN hst

end Rep

section Minors

variable {D : D7} {m n : ℕ}

theorem minor_ne (τ : D.what₂.Tau) (a b k : ℕ) (ha : a + k ≤ m) (hb : b + k ≤ n) :
    (Matrix.of fun α β : Fin k => (varF τ (a + β) (b + α) : MvPolynomial (FVar D m n) ℂ)).det ≠ 0 := by
  intro h
  have h1 := congrArg (MvPolynomial.eval fun x : FVar D m n => if (x.2.1 : ℕ) + b = x.2.2 + a then (1 : ℂ) else 0) h
  rw [RingHom.map_det, map_zero] at h1
  have h2 : (MvPolynomial.eval fun x : FVar D m n => if (x.2.1 : ℕ) + b = x.2.2 + a then (1 : ℂ) else 0).mapMatrix
      (Matrix.of fun α β : Fin k => (varF τ (a + β) (b + α) : MvPolynomial (FVar D m n) ℂ)) = 1 := by
    ext α β
    have hα := α.2
    have hβ := β.2
    have hr : a + β < m ∧ b + α < n := ⟨by omega, by omega⟩
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, varF, dif_pos hr, MvPolynomial.eval_X,
      Matrix.one_apply, Fin.ext_iff]
    exact if_congr ⟨fun h => by omega, fun h => by omega⟩ rfl rfl
  rw [h2, Matrix.det_one] at h1
  exact one_ne_zero h1

theorem delta_ne (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ) (hpq : ∀ τ, p τ + q τ ≤ m) (hmn : m ≤ n) :
    (delta p q ap am : MvPolynomial (FVar D m n) ℂ) ≠ 0 := by
  unfold delta deltaAt
  refine Finset.prod_ne_zero_iff.2 fun τ _ => mul_ne_zero
    (Finset.prod_ne_zero_iff.2 fun i hi => pow_ne_zero _ ?_) (Finset.prod_ne_zero_iff.2 fun i hi => pow_ne_zero _ ?_)
  · have := Finset.mem_range.1 hi
    have := hpq τ
    have h := minor_ne (m := m) (n := n) τ 0 0 (i + 1) (by omega) (by omega)
    simpa only [minorPlus, zero_add] using h
  · have := Finset.mem_range.1 hi
    have := hpq τ
    exact minor_ne (m := m) (n := n) τ (p τ) (n - (i + 1)) (i + 1) (by omega) (by omega)

theorem Delta_ne (i : Fin D.R.m) : RealDat.Delta (D := D) i ≠ 0 := by
  refine delta_ne _ _ _ _ (fun τ => ?_) ((rank_Wc i).le.trans (r_le_V i))
  rw [D.sp.W_sigval _ (Nat.le_add_left _ _) i.2, rank_Wc]
  have := i.2
  simp only [Ranks.sigW, Ranks.r]
  omega

end Minors

section Io

open Formalism.MainNotions.S Formalism.IndefR.Mult

variable {D : D7} {W : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel W S)

theorem model_irred (hs : LowSm M) (hl : ExtLine M) (τ : D.what₂.Tau) (N : Submodule ℂ (M.H τ))
    (hN : N ≤ lowKSub (M.ε τ) (M.lam τ) (M.σ τ)) (hst : IsKStableOn (M.ε τ) (M.σ τ) N) :
    N = ⊥ ∨ N = lowKSub (M.ε τ) (M.lam τ) (M.σ τ) := by
  refine lowK_irred (M.ds τ) (fun w w' h1 h2 h3 h1' h2' h3' => ?_) N hN hst
  obtain ⟨e, he⟩ := exists_isExtVec M hs
  have hu : ∀ (x : M.sm τ), ‖(x : M.H τ)‖ = 1 → (x : M.H τ) ∈ lowKSub (M.ε τ) (M.lam τ) (M.σ τ) →
      IsWtOn (Formalism.REAL.Kset (M.ε τ)) (M.σ τ) (extWt M τ) (x : M.H τ) → IsExtVec M (Function.update e τ x) := by
    intro x a b c ρ
    by_cases h : ρ = τ
    · subst h
      rw [Function.update_self]
      exact ⟨a, b, c⟩
    · rw [Function.update_of_ne h]
      exact he ρ
  obtain ⟨c, -, hc⟩ := hl _ _ (hu ⟨w, hs τ h2⟩ h1 h2 h3) (hu ⟨w', hs τ h2'⟩ h1' h2' h3') τ
  rw [Function.update_self, Function.update_self] at hc
  exact ⟨c, congrArg Subtype.val hc⟩

theorem inj_factor (hs : LowSm M) (hl : ExtLine M) (τ : D.what₂.Tau) {X : Type} [AddCommGroup X] [Module ℂ X]
    (f : LowT M →ₗ[ℂ] X) (om : Matrix (Fin W.rank) (Fin W.rank) ℂ → X →ₗ[ℂ] X)
    (hf : ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ (v : ∀ ρ, lowT M ρ) (u : lowT M τ),
      ((u : M.sm τ) : M.H τ) = M.σ τ k ((v τ : M.sm τ) : M.H τ) →
      om k (f (PiTensorProduct.tprod ℂ v)) = f (PiTensorProduct.tprod ℂ (Function.update v τ u)))
    (v : ∀ ρ, lowT M ρ) (hv : f (PiTensorProduct.tprod ℂ v) ≠ 0) (x : lowT M τ)
    (hx : f (PiTensorProduct.tprod ℂ (Function.update v τ x)) = 0) : x = 0 := by
  let g : lowT M τ →ₗ[ℂ] X := f ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap v τ
  have hg : ∀ y, g y = f (PiTensorProduct.tprod ℂ (Function.update v τ y)) := fun y => rfl
  let j : lowT M τ →ₗ[ℂ] M.H τ := (M.sm τ).subtype ∘ₗ (lowT M τ).subtype
  have hj : Function.Injective j := Subtype.val_injective.comp Subtype.val_injective
  have hst := GlobalTheory.LowKProj.lowKSub_stable (M.ε τ) (M.lam τ) (M.σ τ)
  rcases model_irred M hs hl τ ((LinearMap.ker g).map j) (by rintro _ ⟨y, -, rfl⟩; exact y.2) (by
      rintro k hk _ ⟨y, hy, rfl⟩
      have hm : M.σ τ k (j y) ∈ lowKSub (M.ε τ) (M.lam τ) (M.σ τ) := hst k hk _ y.2
      refine ⟨⟨⟨_, hs τ hm⟩, hm⟩, ?_, rfl⟩
      have := hf k hk (Function.update v τ y) ⟨⟨_, hs τ hm⟩, hm⟩ (by rw [Function.update_self]; rfl)
      rw [Function.update_idem, ← hg, ← hg, (LinearMap.mem_ker.1 hy : g y = 0), map_zero] at this
      exact this.symm) with h | h
  · have : j x ∈ (LinearMap.ker g).map j := ⟨x, hx, rfl⟩
    rw [h, Submodule.mem_bot] at this
    exact hj (this.trans (map_zero j).symm)
  · have : j (v τ) ∈ (LinearMap.ker g).map j := by rw [h]; exact (v τ).2
    obtain ⟨y, hy, hy'⟩ := this
    rw [hj hy'] at hy
    have h0 : g (v τ) = 0 := hy
    rw [hg, Function.update_eq_self] at h0
    exact absurd h0 hv

end Io

theorem ioExt : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.Char F → (∀ i, VStd D i) → (∀ i, LowSm (R.MW i (sg0 D A)) ∧ ExtLine (R.MW i (sg0 D A))) → IoExt R := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR hV hM i
  obtain ⟨hs, hl⟩ := hM i
  obtain ⟨-, hK, v, w, hv1, hw1, hio⟩ := hR.thP.ioP i A.μ0
  obtain ⟨hth, hvac, hcW, hcV, hbW⟩ := GlobalTheory.T.theta_vector_fock_vacuum D G Pl0 T0 A Ks R F hR i A.μ0 (hV i)
  have hP := (GlobalTheory.AdTh.RecPair.isPair_record D G Pl0 T0 A Ks R F hR i A.μ0 (hV i)).1
  have hinj := GlobalTheory.FockVecInj.pureTensorO_injective D R.ψ R.θ (Vc D i) (Wc D i) hP.weil.std hP.inf (fun _ => 1) (R.BV i)
    (cart (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) (fun _ => (Vc D i).rank) (fun τ => ((Wc D i).sig (tauE D τ)).1)
    hcV hcW (hR.models.BV i) hbW hP.sigV hP.sigW _ hth hvac (GlobalTheory.T.theta_vector_ne_zero D G Pl0 T0 A Ks R F hR i (hV i))
  let pt := pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A)))
    (R.vP i A.μ0)
  let f : LowT (R.MW i (sg0 D A)) →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ) := pt ∘ₗ (R.ioP i).flip w
  have hf : ∀ x, f x = R.ptP i A.μ0 (R.ioP i x w) := fun x => rfl
  have hv0 : f (PiTensorProduct.tprod ℂ v) ≠ 0 := by
    rw [hf, hio]
    exact fun h => Delta_ne i (hinj (h.trans (map_zero pt).symm))
  refine ⟨fun ρ => v ρ, fun τ => ⟨hv1 τ, (v τ).2, fun a ha => ?_⟩, v, w, fun _ => rfl, hw1, hio⟩
  have hm := GlobalTheory.LowKProj.lowKSub_stable _ _ _ _ ha _ (v τ).2
  let u : lowT (R.MW i (sg0 D A)) τ := ⟨⟨_, hs τ hm⟩, hm⟩
  have h1 := hK τ _ ha v u rfl w
  rw [hio, GlobalTheory.T.theta_vector_torus_action D G Pl0 T0 A Ks R F hR i (hV i) τ a A.μ0, ← hio, ← hf, ← hf] at h1
  have h2 := inj_factor (R.MW i (sg0 D A)) hs hl τ f
    (fun k => R.ωP i A.μ0 (1, atTau R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ)))
    (fun k hk v u hu => hK τ k hk v u hu w) v hv0
    (u - cexp (((∑ j, extWt (R.MW i (sg0 D A)) τ j * a j : ℝ) : ℂ) * I) • v τ) (by
      rw [MultilinearMap.map_update_sub, MultilinearMap.map_update_smul, Function.update_eq_self, map_sub, map_smul, ← h1,
        sub_self])
  exact congrArg (fun y : lowT (R.MW i (sg0 D A)) τ => ((y : (R.MW i (sg0 D A)).sm τ) : (R.MW i (sg0 D A)).H τ))
    (sub_eq_zero.1 h2)

end GlobalTheory.AdTh.IoExtPf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridConductorIdealCMIsCoprimeHalfDifferent
section
noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum

namespace GlobalTheory.FunObj.StdDatum.HalfDiff

theorem condE_isCoprime_bb {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (h1 : Nat.Coprime D.host.pde (D.host.QS * D.host.q))
    (h2 : Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) : IsCoprime (condE P) D.host.𝔟 :=
  (condE_isCoprime_halfDifferent P ⟨h1, h2⟩).1

end GlobalTheory.FunObj.StdDatum.HalfDiff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridLocalTensorPlacesOverSplitPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LocPlSplit

theorem nonempty_of_not_isConjPl {D : D7} {w : HeightOneSpectrum (𝓞 D.host.E)}
    (h : ¬ Formalism.IndefR.Lev.IsConjPl (D := D) w w) :
    Nonempty (D.host.E →ₐ[D.host.F] Fv D.host.F (w.under (𝓞 D.host.F))) := by
  obtain ⟨-, ι, -⟩ := Formalism.IndefR.Fin.idem_data w h (w.under (𝓞 D.host.F)) rfl
  exact ⟨ι⟩

theorem locPl_split : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (w : HeightOneSpectrum (𝓞 D.host.E)), w ∈ locPl G t →
      Nonempty (D.host.E →ₐ[D.host.F] Fv D.host.F (w.under (𝓞 D.host.F))) := by
  intro D T L sc G μ₀ hL t w hw
  refine nonempty_of_not_isConjPl ?_
  rcases Finset.mem_union.1 hw with h | h
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
    obtain ⟨e, he⟩ := G.pl.w_split v hv
    exact Formalism.IndefR.Fin.idemAt_split he
  · exact (hL.Q_pl t w h).2 w h

end GlobalTheory.LocPlSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.H1VanishingAffineBaseStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstCohomologyVanishes_of_isRelAcyclic_over_spec : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X), M.IsLB → CompactSpace X → GlobalTheory.CxForm.IsRelAcyclic f f M → GlobalTheory.AbLaw.FirstCohomologyVanishes M := by
  first | exact @GlobalTheory.CxForm.firstCohomologyVanishes_of_isRelAcyclic_affine | exact GlobalTheory.CxForm.firstCohomologyVanishes_of_isRelAcyclic_affine | (intros; apply GlobalTheory.CxForm.firstCohomologyVanishes_of_isRelAcyclic_affine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarFundDomainLeCardMulOfTranslateCover
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem measure_fund_le_card_mul_of_cover : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N Λ : Subgroup G) [Countable Λ] (ν : Measure N) (DN : Set N) (b : G) (κ : ℝ≥0∞) (V : Set G) (Y : Finset G), ν.IsHaarMeasure → IsFundamentalDomain (Λ.subgroupOf N) DN ν → IsCompact V → (∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ u : N, f (b * u * b⁻¹) ∂ν = κ * ∫⁻ u : N, f u ∂ν) → (∀ y ∈ Y, y ∈ N) → (∀ u ∈ N, ∃ γ ∈ Λ, γ ∈ N ∧ ∃ y ∈ Y, ∃ w ∈ V, γ * u = y * b⁻¹ * w * b) → ν DN ≤ Y.card * (κ * ν {u | (u : G) ∈ V}) := by
  intro G _ _ _ _ _ _ _ _ N Λ _ ν DN b κ V Y hν hD hV hconj hY hcov
  have hVm : MeasurableSet V := hV.isClosed.measurableSet
  have hconjm : Measurable fun u : N => b * (u : G) * b⁻¹ :=
    (measurable_const.mul measurable_subtype_coe).mul measurable_const
  have hS₀m : MeasurableSet {u : N | b * (u : G) * b⁻¹ ∈ V} := hconjm hVm
  have hVNm : MeasurableSet {u : N | (u : G) ∈ V} := measurable_subtype_coe hVm
  have hS₀ : ν {u : N | b * (u : G) * b⁻¹ ∈ V} = κ * ν {u : N | (u : G) ∈ V} := by
    have h := hconj (V.indicator 1) (measurable_one.indicator hVm)
    have e1 : (fun u : N => V.indicator (1 : G → ℝ≥0∞) (b * u * b⁻¹))
        = {u : N | b * (u : G) * b⁻¹ ∈ V}.indicator 1 := by
      ext u; simp [Set.indicator]
    have e2 : (fun u : N => V.indicator (1 : G → ℝ≥0∞) u) = {u : N | (u : G) ∈ V}.indicator 1 := by
      ext u; simp [Set.indicator]
    rw [e1, e2, lintegral_indicator hS₀m, lintegral_indicator hVNm] at h
    simpa using h
  have hΛN : Countable (Λ.subgroupOf N) := by
    refine Function.Injective.countable (f := fun x : Λ.subgroupOf N => (⟨(x : N), x.2⟩ : Λ)) ?_
    intro x y h
    apply Subtype.ext; apply Subtype.ext
    simpa using congrArg (fun z : Λ => (z : G)) h
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup (Λ.subgroupOf N)
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup (Λ.subgroupOf N) ν
  let T : G → Set N := fun y => {v : N | b * (y⁻¹ * (v : G)) * b⁻¹ ∈ V}
  have hle : ν DN ≤ ν (⋃ y ∈ Y, T y) := by
    refine GlobalTheory.measure_le_of_isFundamentalDomain_of_ae_covers hD (.of_forall fun u => ?_)
    obtain ⟨γ, hγΛ, hγN, y, hy, w, hw, heq⟩ := hcov u u.2
    refine ⟨⟨⟨γ, hγN⟩, (Subgroup.mem_subgroupOf).2 hγΛ⟩, Set.mem_biUnion hy ?_⟩
    show b * (y⁻¹ * (γ * (u : G))) * b⁻¹ ∈ V
    rw [heq]
    convert hw using 1
    group
  have hT : ∀ y ∈ Y, ν (T y) = κ * ν {u : N | (u : G) ∈ V} := by
    intro y hy
    have hyN : y⁻¹ ∈ N := N.inv_mem (hY y hy)
    have : T y = (fun v : N => (⟨y⁻¹, hyN⟩ : N) * v) ⁻¹' {u : N | b * (u : G) * b⁻¹ ∈ V} := by
      ext v; simp [T, mul_assoc]
    rw [this, measure_preimage_mul, hS₀]
  refine hle.trans ((measure_biUnion_finset_le _ _).trans ?_)
  rw [Finset.sum_congr rfl hT, Finset.sum_const, nsmul_eq_mul]

end GlobalTheory.SphEis
end


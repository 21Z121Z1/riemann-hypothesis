import Mathlib
import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSplitIdempotentsOfRelTraceOneModTwo
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0005
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.IntegralCoordinatesNorm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTermsNormsIndependentRepresenta
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0133
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsReparametrizationByTowerParameter
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0094
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLocalValueOfQuotientAddOfCommonDenominator
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0250
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionPointPadicAbscissaNormLeOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0300

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSplitAt
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MovedSplit

open GlobalTheory.SplitIdem GlobalTheory.IdemModTwo

theorem idem_alg {T : Type} [CommRing T] (p U R w w' : T) (hU : p * U = U)
    (hR : R * R - (w + w') * R + w * w' * p = 0) (hδ : (w + w') * U - 2 * (U * R) = p) :
    (U * w - U * R) * (U * w - U * R) = U * w - U * R ∧
      (U * w - U * R) * (U * w' - U * R) = 0 ∧
      (U * w - U * R) + (U * w' - U * R) = p := by
  have h2 : (U * w - U * R) * (U * w' - U * R) = 0 := by
    linear_combination U * U * hR - w * w' * U * hU
  refine ⟨?_, h2, by linear_combination hδ⟩
  linear_combination (U * w - U * R) * hδ - h2 + (w - R) * hU

theorem idem_tensor {F A E K : Type} [Field F] [CommRing A] [Algebra F A] [CommRing E] [Algebra F E]
    [CommRing K] [Algebra F K] (φ : K →ₙ+* A)
    (hφ : ∀ (t : F) (y : K), φ (algebraMap F K t * y) = algebraMap F A t * φ y)
    (c : A ⊗[F] E →+* A ⊗[F] E) (a b : E) (t n : F) (r u : K)
    (hc1 : ∀ x : A, c (x ⊗ₜ 1) = x ⊗ₜ 1) (hca : ∀ x : A, c (x ⊗ₜ a) = x ⊗ₜ b)
    (ht : algebraMap F E t = a + b) (hn : algebraMap F E n = a * b)
    (hr : r * r - algebraMap F K t * r + algebraMap F K n = 0) (hu : u * (algebraMap F K t - 2 * r) = 1)
    (e : A ⊗[F] E) (he : e = φ u ⊗ₜ a + φ (-(u * r)) ⊗ₜ 1) :
    e * e = e ∧ e * c e = 0 ∧ e + c e = algebraMap A (A ⊗[F] E) (φ 1) := by
  let j : A →+* A ⊗[F] E := algebraMap A _
  let k : E →+* A ⊗[F] E := (Algebra.TensorProduct.includeRight : E →ₐ[F] A ⊗[F] E)
  have hjk : ∀ a x, a ⊗ₜ[F] x = j a * k x := fun a x => by
    simp [j, k, Algebra.TensorProduct.tmul_mul_tmul]
  have hF : ∀ s : F, j (algebraMap F A s) = k (algebraMap F E s) := fun s => by
    have h := hjk 1 (algebraMap F E s)
    rw [tmul_algebraMap_eq, mul_one, map_one, one_mul] at h
    exact h
  have h1 : e = j (φ u) * k a - j (φ u) * j (φ r) := by
    rw [he, hjk, hjk, map_neg, map_mul, map_neg, map_mul, map_one]; ring
  have h2 : c e = j (φ u) * k b - j (φ u) * j (φ r) := by
    rw [he, map_add, hc1, hca, hjk, hjk, map_neg, map_mul, map_neg, map_mul, map_one]; ring
  rw [h2, h1]
  refine idem_alg (j (φ 1)) _ _ _ _ ?_ ?_ ?_
  · rw [← map_mul, ← map_mul, one_mul]
  · have : φ r * φ r - algebraMap F A t * φ r + algebraMap F A n * φ 1 = 0 := by
      rw [← hφ, ← hφ, ← map_mul, ← map_sub, ← map_add, mul_one, hr, map_zero]
    have h := congrArg j this
    rwa [map_add, map_sub, map_mul, map_mul, map_mul, hF, hF, ht, hn, map_add, map_mul, map_zero] at h
  · have : algebraMap F A t * φ u - 2 * (φ u * φ r) = φ 1 := by
      rw [two_mul, ← hφ, ← map_mul, ← map_add, ← map_sub, ← hu]; congr 1; ring
    have h := congrArg j this
    rwa [map_sub, map_mul, map_mul, map_mul, map_ofNat, hF, ht, map_add] at h

theorem exists_root (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (t n : 𝓞 F)
    (ht : t ∉ v.asIdeal) (hn : n ∈ v.asIdeal) :
    ∃ r u : v.adicCompletionIntegers F,
      r * r - algebraMap (𝓞 F) (v.adicCompletionIntegers F) t * r +
        algebraMap (𝓞 F) (v.adicCompletionIntegers F) n = 0 ∧
      u * (algebraMap (𝓞 F) (v.adicCompletionIntegers F) t - 2 * r) = 1 := by
  haveI := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  have hm : algebraMap (𝓞 F) (v.adicCompletionIntegers F) n ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff]
    exact fun h => h hn
  have hT : IsUnit (algebraMap (𝓞 F) (v.adicCompletionIntegers F) t) :=
    (GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff v t).2 ht
  generalize algebraMap (𝓞 F) (v.adicCompletionIntegers F) t = T at hT
  generalize algebraMap (𝓞 F) (v.adicCompletionIntegers F) n = N at hm
  obtain ⟨r, hr, hr0⟩ := HenselianRing.is_henselian (I := IsLocalRing.maximalIdeal (v.adicCompletionIntegers F))
    (Polynomial.X ^ 2 - Polynomial.C T * Polynomial.X + Polynomial.C N) (by monicity!) 0
    (by simpa using hm) (by simpa using hT.map _)
  rw [sub_zero] at hr0
  have hunit : IsUnit (T - 2 * r) := by
    by_contra h
    have h1 : T - 2 * r ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := h
    have h2 := Ideal.add_mem _ h1 (Ideal.mul_mem_left _ 2 hr0)
    rw [sub_add_cancel] at h2
    exact h2 hT
  obtain ⟨u, hu⟩ := hunit.exists_left_inv
  refine ⟨r, u, ?_, hu⟩
  simpa [Polynomial.IsRoot, pow_two] using hr

theorem exists_int (D : D7) (x : 𝓞 D.host.E) (hx : star (x : D.host.E) = x) :
    ∃ t : 𝓞 D.host.F, algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t = x ∧
      algebraMap D.host.F D.host.E (t : D.host.F) = x := by
  obtain ⟨t, ht⟩ := exists_of_star_eq D hx
  have hi : IsIntegral ℤ t :=
    (isIntegral_algebraMap_iff (algebraMap D.host.F D.host.E).injective).1 (ht ▸ x.2)
  exact ⟨⟨t, hi⟩, RingOfIntegers.ext ht, ht⟩

theorem exists_splitAt : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)), GlobalTheory.UnRep.SplitPl (GlobalTheory.Member.cF D) v → ∃ e : Formalism.L2.Theta.AE D, GlobalTheory.IdemModTwo.SplitAt D v e := by
  rintro D v ⟨P, hP, hPv, a, ha, b, hb, hbP⟩
  have hb' : (b : D.host.E) = star (a : D.host.E) := hb
  obtain ⟨t, ht, ht'⟩ := exists_int D (a + b) (by
    show star ((a : D.host.E) + b) = (a : D.host.E) + b
    rw [hb', star_add, star_star, add_comm])
  obtain ⟨n, hn, hn'⟩ := exists_int D (a * b) (by
    show star ((a : D.host.E) * b) = (a : D.host.E) * b
    rw [hb', star_mul', star_star, mul_comm])
  have htv : t ∉ v.asIdeal := by
    rw [← hPv, Ideal.mem_comap, ht]
    exact fun h => hbP ((Ideal.add_mem_iff_right P ha).1 h)
  have hnv : n ∈ v.asIdeal := by
    rw [← hPv, Ideal.mem_comap, hn]
    exact Ideal.mul_mem_right _ _ ha
  obtain ⟨r, u, hr, hu⟩ := exists_root D.host.F v t n htv hnv
  have key := idem_tensor (placeHom D.host.F v) (fun s y => by
      refine Prod.ext (mul_zero _).symm ?_
      show singleV D.host.F v _ = algebraMap D.host.F (Af D.host.F) s * singleV D.host.F v y
      rw [singleV_mul, AlgHom.commutes])
    (cA D) (a : D.host.E) (b : D.host.E) (t : D.host.F) (n : D.host.F) (r : Fv D.host.F v) (u : Fv D.host.F v)
    (fun x => by rw [cA_tmul, star_one]) (fun x => by rw [cA_tmul, hb']) ht' hn'
    (congrArg Subtype.val hr) (congrArg Subtype.val hu) _ rfl
  exact ⟨_, key⟩

end GlobalTheory.MovedSplit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTotallyComplexExt
section
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open GlobalTheory.NormSum GlobalTheory.IndefiniteRowSideFullHecke.IntegralCoordinatesNorm

namespace GlobalTheory.NormSum.Compare

theorem sqrt_le_rd (D : D7) : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ D.host.rdE :=
  (UpperTheory.KR.log_qd_le_rd D.host.toHostAx D.host.flPS).2.2.1

theorem three_le (D : D7) : (3 : ℝ) ≤ D.host.q ∧ (3 : ℝ) ≤ D.host.d := by
  obtain ⟨hq, hd, -, hq2, hd2⟩ := D.host.hypOdd
  have := hq.two_le
  have := hd.two_le
  constructor
  · exact_mod_cast (show 3 ≤ D.host.q by omega)
  · exact_mod_cast (show 3 ≤ D.host.d by omega)

theorem log_d_le (D : D7) : Real.log D.host.d ≤ 2 * Real.log D.host.rdE := by
  obtain ⟨hq, hd⟩ := three_le D
  have h2 := sqrt_le_rd D
  have h3 := Real.sq_sqrt (show (0 : ℝ) ≤ (D.host.q : ℝ) * D.host.d by positivity)
  have h4 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 2
  have h5 : (D.host.d : ℝ) ≤ D.host.rdE ^ 2 := by nlinarith
  have := Real.log_le_log (by linarith) h5
  rwa [Real.log_pow, Nat.cast_ofNat] at this

def ArchOne (G : D7 → ℕ → Prop) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ) (Q : ℕ), Crv D cc δ →
    GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → G D Q →
    ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (σ : K →+* ℂ) (ι : Type) (N : ℕ) (B L : ℝ)
      (P P' : ι → Pair D cc δ t0 Q) (zA zA' : ι → K),
      1 ≤ N → 1 ≤ B → 1 ≤ L → Real.log D.host.rdE ≤ L → |logDerivativeAtOne D| ≤ L →
      (∀ i, (P i).Small N B ∧ (P' i).Small N B) →
      (∀ i, σ (zA i) = ((P i).norm : ℂ) ∧ σ (zA' i) = ((P' i).norm : ℂ)) →
      ArchimedeanHeightBound zA zA' (bArch C (fF D) N B L Q)

def ArchAny (G : D7 → ℕ → Prop) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (N : ℕ) (B L : ℝ) (Q : ℕ), 1 ≤ N ∧ 1 ≤ B ∧ G D Q ∧ Real.log D.host.rdE ≤ L →
    Real.log D.host.d ≤ L → |logDerivativeAtOne D| ≤ L →
    ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (emb : K →+* ℂ) (ι : Type) (zA zA' : ι → K),
      (∀ ij, IsNorm D Set.univ N B Q (emb (zA ij)) ∧ IsNorm D Set.univ N B Q (emb (zA' ij))) →
      ArchimedeanHeightBound zA zA' (bArch C (fF D) N B L Q)

theorem ArchOne.mono {G G' : D7 → ℕ → Prop} (hG : ∀ D Q, G' D Q → G D Q) (h : ArchOne G) : ArchOne G' := by
  obtain ⟨C, hC, h⟩ := h
  exact ⟨C, hC, fun D cc δ t0 Q h1 h2 h3 => h D cc δ t0 Q h1 h2 (hG D Q h3)⟩

def NormNeZero : Prop :=
  ∀ (D : D7) (δ t0 : ℂ) (Q : ℕ), GoodLevel D Q → ∀ P : Pair D ⊤ δ t0 Q, (∃ h T, P.coord h T ≠ 0) → P.norm ≠ 0

def IsNormAt (D : D7) (δ t0 : ℂ) (N : ℕ) (B : ℝ) (Q : ℕ) (x : ℂ) : Prop :=
  ∃ P : Pair D ⊤ δ t0 Q, P.Small N B ∧ x = (P.norm : ℂ)

def IntAt : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (N : ℕ) (B L : ℝ) (Q : ℕ), Sizes D N B L Q → ∀ δ t0 : ℂ, Curve D ⊤ δ t0 →
    ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (emb : K →+* ℂ),
      ∃ dl : Formalism.PairingDivisionLocalBalance.Pl K → ℝ, ∀ (ι : Type) (zA zA' : ι → K),
        (∀ ij, IsNormAt D δ t0 N B Q (emb (zA ij)) ∧ IsNormAt D δ t0 N B Q (emb (zA' ij))) →
        (∀ ij, zA ij ≠ 0 ∧ zA' ij ≠ 0) → NonArchimedeanDefectBound dl zA zA' (bInt C (fF D) N B L Q)

section Places

open Formalism.DivisionValues (vw lw)
open Formalism.PairingDivisionLocalBalance (Pl)
open IsDedekindDomain

variable {K : Type} [Field K] [NumberField K]

end Places

def raise {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q Q₁ : ℕ} (P : Pair D cc δ t0 Q) (hd : Q ∣ Q₁) (h0 : 0 < Q₁) :
    Pair D cc δ t0 Q₁ :=
  { P with
    pres := by
      obtain ⟨k, r, z, h1, h2, h3, h4⟩ := P.pres
      have hle : Q ≤ Q₁ := Nat.le_of_dvd h0 hd
      obtain ⟨m, rfl⟩ := hd
      refine ⟨k, r, z, fun i => ?_, fun i => ?_, fun ρ => (h3 ρ).trans ?_, h4⟩
      · rw [mul_comm, mul_smul]
        exact AddSubgroup.nsmul_mem _ (h1 i) m
      · have e : ((Q * m : ℕ) : Qbar) ^ (P.a * P.d) * r i =
            ((m ^ (P.a * P.d) : ℕ) : Qbar) * ((Q : Qbar) ^ (P.a * P.d) * r i) := by
          push_cast; ring
        rw [e]
        exact (isIntegral_natCast _).mul (h2 i)
      · exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hle) _
    idx_le := P.idx_le.trans (Nat.pow_le_pow_left (Nat.le_of_dvd h0 hd) _) }

def CoordClauses {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (l : ℕ) [Fact l.Prime]
    (e_vp : ℝ) : Prop :=
  (∀ h : GA D P.d, ∃ γ ∈ ratG D P.d, ∃ j ∈ P.J, IntOver D l (γ * h * j)) ∧
    (∀ h : GA D P.d, gam D P.J h ≠ 0 ∧ (padicValNat l (gam D P.J h) : ℝ) ≤ e_vp) ∧
    ∀ h : GA D P.d, IntOver D l h → ∀ T, ∃ hz : P.coord h T ∈ Qbar,
      ∀ lam : Qbar →+* ℂ_[l], ‖lam ⟨P.coord h T, hz⟩‖ ≤ (l : ℝ) ^ e_vp

theorem CoordClauses.mono {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} {P : Pair D cc δ t0 Q} {l : ℕ}
    [hl : Fact l.Prime] {e e' : ℝ} (h : CoordClauses P l e) (he : e ≤ e') : CoordClauses P l e' :=
  ⟨h.1, fun g => ⟨(h.2.1 g).1, (h.2.1 g).2.trans he⟩, fun g hg T => (h.2.2 g hg T).imp fun _ hb lam =>
    (hb lam).trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hl.out.one_le) he)⟩

def CoordsLev (D : D7) (G : ℕ → Prop) (N : ℕ) (B : ℝ) (Q : ℕ) (del_vp : ℕ → ℝ) : Prop :=
  ∀ (δ t0 : ℂ) (l : ℕ) [Fact l.Prime] (Q' : ℕ), G Q' → Nat.Coprime Q' l → ∀ P : Pair D ⊤ δ t0 (Q * Q'), P.Small N B →
    CoordClauses P l (del_vp l)

def NormNeZeroAt (D : D7) (N : ℕ) (B : ℝ) (Q : ℕ) : Prop :=
  ∀ (δ t0 : ℂ) (P : Pair D ⊤ δ t0 Q), P.Small N B → (∃ h T, P.coord h T ≠ 0) → P.norm ≠ 0

def IntLev (G : D7 → ℕ → Prop) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (N : ℕ) (B L : ℝ) (Q : ℕ), Sizes D N B L Q →
    ∃ (S : Finset ℕ) (del_vp : ℕ → ℝ), Del S del_vp (bInt C (fF D) N B L Q) ∧
      CoordsLev D (G D) N B Q del_vp ∧ NormsInt D {⊤} N B Q S del_vp (bInt C (fF D) N B L Q)

def CoordOnly (G : D7 → ℕ → Prop) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (N : ℕ) (B L : ℝ) (Q : ℕ), Sizes D N B L Q →
    ∃ (S : Finset ℕ) (del_vp : ℕ → ℝ), Del S del_vp (bInt C (fF D) N B L Q) ∧ CoordsLev D (G D) N B Q del_vp

theorem IntLev.mono {G G' : D7 → ℕ → Prop} (hG : ∀ D Q, G' D Q → G D Q) (h : IntLev G) : IntLev G' := by
  obtain ⟨C, hC, h⟩ := h
  refine ⟨C, hC, fun D N B L Q hs => ?_⟩
  obtain ⟨S, del, h1, h2, h3⟩ := h D N B L Q hs
  exact ⟨S, del, h1, fun δ t0 l _ Q' hQ => h2 δ t0 l Q' (hG D Q' hQ), h3⟩

end GlobalTheory.NormSum.Compare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqProdLocalComponentsApproximating
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CharLocProd

noncomputable def evalAt {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) :
    FiniteAdeleRing (𝓞 E) E →+* P.adicCompletion E where
  toFun x := x P
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem val_algebraMap {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (a : E) :
    Valued.v (algebraMap E (P.adicCompletion E) a) = P.valuation E a :=
  P.valuedAdicCompletion_eq_valuation' a

theorem evalAt_algebraMap {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (a : E) :
    evalAt P (algebraMap E (FiniteAdeleRing (𝓞 E) E) a) = algebraMap E (P.adicCompletion E) a := rfl

theorem eq_prod_of_components {E : Type} [Field E] [NumberField E] {R A B : Type} [CommRing R] [CommRing A]
    [CommRing B] (p : R →+* A) (q : R →+* B) (inc : E →+* R)
    (ev : ∀ P : HeightOneSpectrum (𝓞 E), B →+* P.adicCompletion E)
    (hinc : ∀ P a, ev P (q (inc a)) = algebraMap E _ a)
    (I : AddSubgroup B) (hint : ∀ y, y ∈ I ↔ ∀ P, Valued.v (ev P y) ≤ 1)
    (e : HeightOneSpectrum (𝓞 E) → R) (hinf : ∀ P, p (e P) = 0) (h1 : ∀ P, ev P (q (e P)) = 1)
    (h0 : ∀ P P', P' ≠ P → ev P' (q (e P)) = 0) (c : Rˣ →* Circle) (N : ℕ) (hN : 0 < N)
    (hker : ∀ x : Rˣ, (p x = 1 ∧ q x ∈ I ∧ q (x⁻¹ : Rˣ) ∈ I) → (∃ y ∈ I, q x - 1 = N • y) → c x = 1)
    (x : Rˣ) (hx : p x = 1) (S : Finset (HeightOneSpectrum (𝓞 E))) (k : HeightOneSpectrum (𝓞 E) → Eˣ)
    (l : HeightOneSpectrum (𝓞 E) → Rˣ) (hl : ∀ P, (l P : R) = 1 + e P * (inc (k P) - 1))
    (hS : ∀ P ∈ S, Valued.v (ev P (q x)) = P.valuation E (k P : E) ∧
      Valued.v (ev P (q x) - algebraMap E _ (k P : E)) ≤ P.valuation E (N : E) * P.valuation E (k P : E))
    (hS' : ∀ P, P ∉ S → Valued.v (ev P (q x)) = 1 ∧ (N : 𝓞 E) ∉ P.asIdeal) :
    c x = ∏ P ∈ S, c (l P) := by
  classical
  obtain ⟨u, hud⟩ : ∃ u : Rˣ, u = ∏ P ∈ S, l P := ⟨_, rfl⟩
  have hu : (u : R) = ∏ P ∈ S, (l P : R) := by
    simp only [hud, Units.coe_prod]
  have huinf : p u = 1 := by
    rw [hu, map_prod]
    refine Finset.prod_eq_one fun P _ => ?_
    simp [hl, hinf]
  have hloc1 : ∀ P, ev P (q (l P)) = algebraMap E _ (k P : E) := by
    intro P
    simp only [hl, map_add, map_mul, map_sub, map_one, h1, hinc]
    ring
  have hloc0 : ∀ P Q, Q ≠ P → ev Q (q (l P)) = 1 := by
    intro P Q hQ
    simp only [hl, map_add, map_mul, map_sub, map_one, h0 P Q hQ]
    ring
  have huS : ∀ P ∈ S, ev P (q u) = algebraMap E _ (k P : E) := by
    intro P hP
    rw [hu, map_prod, map_prod, Finset.prod_eq_single P, hloc1]
    · intro Q _ hQ; exact hloc0 Q P hQ.symm
    · intro h; exact absurd hP h
  have huS' : ∀ P, P ∉ S → ev P (q u) = 1 := by
    intro P hP
    rw [hu, map_prod, map_prod]
    refine Finset.prod_eq_one fun Q hQ => hloc0 Q P ?_
    rintro rfl; exact hP hQ
  obtain ⟨y, hy⟩ : ∃ y : Rˣ, y = x * u⁻¹ := ⟨_, rfl⟩
  have hxu : x = y * u := by rw [hy, inv_mul_cancel_right]
  have hyu : (y : R) * u = x := by
    rw [← Units.val_mul, hxu]
  have hyinf : p y = 1 := by
    have := congrArg p hyu
    rwa [map_mul, huinf, hx, mul_one] at this
  have hyev : ∀ P, ev P (q y) * ev P (q u) = ev P (q x) := by
    intro P
    rw [← map_mul, ← map_mul, hyu]
  have hk0 : ∀ P : HeightOneSpectrum (𝓞 E), P.valuation E (k P : E) ≠ 0 :=
    fun P => (Valuation.ne_zero_iff _).2 (k P).ne_zero
  have hN0 : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  have hyv : ∀ P, Valued.v (ev P (q y)) = 1 := by
    intro P
    have := congrArg Valued.v (hyev P)
    rw [map_mul] at this
    by_cases hP : P ∈ S
    · rw [huS P hP, val_algebraMap, (hS P hP).1] at this
      exact mul_right_cancel₀ (hk0 P) (by rw [this, one_mul])
    · rwa [huS' P hP, map_one, mul_one, (hS' P hP).1] at this
  have hyv' : ∀ P, Valued.v (ev P (q (y⁻¹ : Rˣ))) = 1 := by
    intro P
    have : Valued.v (ev P (q y)) * Valued.v (ev P (q (y⁻¹ : Rˣ))) = 1 := by
      rw [← map_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, map_one]
    rwa [hyv, one_mul] at this
  have hcong : ∀ P, Valued.v (ev P (q y) - 1) ≤ P.valuation E (N : E) := by
    intro P
    by_cases hP : P ∈ S
    · have h2 := (hS P hP).2
      rw [← hyev P, huS P hP, ← sub_one_mul, map_mul, val_algebraMap] at h2
      exact le_of_mul_le_mul_right h2 (zero_lt_iff.2 (hk0 P))
    · have h2 : P.valuation E (N : E) = 1 := by
        have := (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := E) P
          (r := (N : 𝓞 E))).2 (hS' P hP).2
        simpa using this
      rw [h2]
      exact Valuation.map_sub_le _ (hyv P).le (by rw [map_one])
  have hcy : c y = 1 := by
    refine hker y ⟨hyinf, (hint _).2 fun P => (hyv P).le, (hint _).2 fun P => (hyv' P).le⟩
      ⟨q (inc (N : E)⁻¹) * (q y - 1), (hint _).2 fun P => ?_, ?_⟩
    · rw [map_mul, map_mul, hinc, val_algebraMap, map_sub, map_one, map_inv₀]
      have hv : 0 < P.valuation E (N : E) :=
        zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hN0)
      exact (inv_mul_le_one₀ hv).2 (hcong P)
    · rw [nsmul_eq_mul, ← mul_assoc, ← map_natCast (q.comp inc) N,
        RingHom.comp_apply, ← map_mul, ← map_mul, mul_inv_cancel₀ hN0, map_one, map_one, one_mul]
  rw [hxu, map_mul, hcy, one_mul, hud, map_prod]

theorem char_eq_prod_locK : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x) → (∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) → (∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ e : AE D, IsPlIdem D e P ∧ infPart D e = 0 ∧ ι (finPart D e) P = 1 ∧ ∀ P' : HeightOneSpectrum (𝓞 D.host.E), P' ≠ P → ι (finPart D e) P' = 0) → ∀ (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E), ChrEq c χ → ∃ N : ℕ, 0 < N ∧ ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ∀ (S : Finset (HeightOneSpectrum (𝓞 D.host.E))) (k : HeightOneSpectrum (𝓞 D.host.E) → D.host.Eˣ), (∀ P ∈ S, Valued.v (ι (finPart D (x : AE D)) P) = P.valuation D.host.E (k P : D.host.E) ∧ Valued.v (ι (finPart D (x : AE D)) P - algebraMap D.host.E _ (k P : D.host.E)) ≤ P.valuation D.host.E (N : D.host.E) * P.valuation D.host.E (k P : D.host.E)) → (∀ P, P ∉ S → Valued.v (ι (finPart D (x : AE D)) P) = 1 ∧ (N : 𝓞 D.host.E) ∉ P.asIdeal) → ((c x : Circle) : ℂ) = ∏ P ∈ S, ((χ.locK P (k P) : ℂˣ) : ℂ) := by
  intro D ι hι hint hidem c χ hc
  obtain ⟨N, hN, hker, -⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D c hc.1.1
  refine ⟨N, hN, fun x hx S k hS hS' => ?_⟩
  choose e he hinf h1 h0 using hidem
  have key := eq_prod_of_components (infPart D) (finPart D) (incA D)
    (fun P => (evalAt P).comp ι.toRingHom)
    (fun P a => (congrArg (evalAt P) (hι a)).trans (evalAt_algebraMap P a))
    (intAE D) hint e hinf h1 h0 c N hN hker x hx S k (fun P => locU (he P).1 (k P)) (fun _ => rfl) hS hS'
  rw [key]
  exact (map_prod Circle.coeHom _ _).trans
    (Finset.prod_congr rfl fun P _ => hc.2 P (e P) (he P) (k P) _ rfl)

end GlobalTheory.CharLocProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IoConstOfMem
section
noncomputable section

namespace GlobalTheory.Glue.IoInh

open GlobalTheory.K5 GlobalTheory.KZ

section Local

variable {p : ℕ} [hp : Fact p.Prime] {Ωl : Type} [Field Ωl] [Algebra (O0 p) Ωl]

theorem ev_single (ψ : O0 p →+* Ωl) (e : Ωl) (h1 : IsInt p e) (h2 : IsAlgZp p e) (a : Lau p) (c : ℤ → Ωl)
    (hc : ∀ r, c r = e * zp Ωl (a.coeff r)) :
    Ev ψ c (e * ψ (algebraMap (Lau p) (O0 p) a)) (e * ψ (algebraMap (Lau p) (O0 p) (thL a))) :=
  ⟨1, fun _ => e, fun _ => a, fun _ => ⟨h1, h2⟩, fun r => by simp [hc], by simp, by simp⟩

theorem zp_intCast (m : ℤ) : zp Ωl (m : ℤ_[p]) = (m : Ωl) := by
  rw [zp, ← HahnSeries.C_apply, map_intCast, map_intCast, map_intCast]

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem const_mem (X : GlobalTheory.KZ.Tower Ω ε) (L : ℕ) (c : Ω) : algebraMap Ω X.K c ∈ KT X L :=
  (X.sl _).commutes c

theorem exp_const (X : GlobalTheory.KZ.Tower Ω ε) (c : Ω) (r : ℚ) :
    (X.exp (algebraMap Ω X.K c)).coeff r = if r = 0 then c else 0 := by
  rw [AlgHom.commutes, HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, HahnSeries.ofPowerSeries_C, HahnSeries.C_apply, HahnSeries.coeff_single]
  split_ifs <;> rfl

variable {X : GlobalTheory.KZ.Tower Ω ε} {A : ValuationSubring Ω} {T : GlobalTheory.K5.Tower p Ωl} {j : Ω →+* Ωl} {n : ℕ}
  {ψ : O0 p →+* Ωl} {io : KT X (p ^ n) →+* Ωl}

theorem io_const_of_mem (h : IsClo p Ωl) (hc : IsCusp ε A T j) (hψ : IsReb T n ψ) (hio : IsIo X A T j n ψ io)
    (c : Ω) (hA : c ∈ A) : io ⟨algebraMap Ω X.K c, const_mem X _ c⟩ = j c := by
  classical
  obtain ⟨x', hx⟩ := hio.ev ⟨algebraMap Ω X.K c, const_mem X _ c⟩ {c} (fun r => by
    simp only [exp_const]
    split_ifs
    · exact ⟨hA, IntermediateField.subset_adjoin _ _ (by simp)⟩
    · exact ⟨zero_mem _, zero_mem _⟩)
  have hp0 : (p : ℚ) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  have h2 := ev_single ψ (j c) ((hc.int c).1 hA) (hc.alg c) 1
    (fun r : ℤ => j ((X.exp (algebraMap Ω X.K c)).coeff ((r : ℚ) / (p : ℚ) ^ n))) (fun r => by
      simp only [exp_const]
      by_cases hr : r = 0
      · subst hr
        have : zp Ωl (1 : ℤ_[p]) = 1 := by simpa using zp_intCast (p := p) (Ωl := Ωl) 1
        simp [this]
      · have : zp Ωl (0 : ℤ_[p]) = 0 := by simpa using zp_intCast (p := p) (Ωl := Ωl) 0
        have h3 : (r : ℚ) / (p : ℚ) ^ n ≠ 0 := div_ne_zero (by exact_mod_cast hr) hp0
        simp [this, h3, HahnSeries.coeff_one, hr])
  have := (GlobalTheory.EvUniq.ev_unique p Ωl h T n ψ hψ _ _ _ _ _ hx h2).1
  rwa [map_one, map_one, mul_one] at this

theorem io_const (h : IsClo p Ωl) (hc : IsCusp ε A T j) (hψ : IsReb T n ψ) (hio : IsIo X A T j n ψ io)
    (c : Ω) : io ⟨algebraMap Ω X.K c, const_mem X _ c⟩ = j c := by
  rcases A.mem_or_inv_mem c with hA | hA
  · exact io_const_of_mem h hc hψ hio c hA
  · have h1 := io_const_of_mem h hc hψ hio c⁻¹ hA
    have h2 : (⟨algebraMap Ω X.K c⁻¹, const_mem X _ c⁻¹⟩ : KT X (p ^ n)) = ⟨algebraMap Ω X.K c, const_mem X _ c⟩⁻¹ :=
      Subtype.ext (map_inv₀ _ _)
    rw [h2, map_inv₀, map_inv₀] at h1
    exact inv_injective h1

end Local

end GlobalTheory.Glue.IoInh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormPadicModelAbscissaLeOneOfTorsionCoprime
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.TorsionAbscissa

theorem norm_xAt_le_of_mul : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p), GL3Theta.At D cc δ g → ∀ (N : ℕ) (v : ℂ), 0 < N → Nat.Coprime N p → (N : ℂ) * v ∈ g.abelian₂ → v ∉ g.abelian₂ → ‖GlobalTheory.EvenTheta.xAt g v‖ ≤ 1 := by
  intro D p _ cc δ g hg N v hN hcop hNv hv
  exact norm_xAt_le D p cc δ g hg v ⟨hv, N, hN, hcop, hNv⟩

end GlobalTheory.TorsionAbscissa
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormThetaTranslateValueAtZeroPadicPeriodicStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_thetaTranslateValueAtZeroPadic_periodic : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p),
    GL3Theta.At D cc δ g → ∀ t ω : ℂ, InRationalLattice g.abelian₂ t → ω ∈ g.abelian₂ → ‖GlobalTheory.ThetaTransl.cval g (t + ω)‖ = ‖GlobalTheory.ThetaTransl.cval g t‖ := by
  first | exact @GlobalTheory.ThetaTransl.cval_norm_periodic | exact GlobalTheory.ThetaTransl.cval_norm_periodic | (intros; apply GlobalTheory.ThetaTransl.cval_norm_periodic <;> assumption)
end


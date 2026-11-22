import Formalism.SharpRestriction.GrowthBounds.CornerGLContinuity
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.LocalRingCardinality.HostCls
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.SharpRestriction.AdmissibleParameterJoins.Bundle0001
import Formalism.SharpRestriction.Bundle0002
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces
import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0010
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0012
import Formalism.GradedWeylDivisibility.FinalC

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.GandSk
section
noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.FrobeniusOrbits NumberField

private theorem hH_hP (D : D7) (p : ℕ) (hp : p.Prime) (hc : IsResidueClassZero D p) :
    ∃ h : Nat.Coprime p 2, D.R.hH (D.R.iota (hP D p)) =
      hcl D.R.e (ZMod.unitOfCoprime p (Nat.Coprime.pow_right (D.R.e + 2) h)) := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : D.host.cls 2 = PrimeClass.ram2 := Formalism.BasicNotions.primeClass_two D.host.toHostRaw
    have hc' : D.host.cls 2 = PrimeClass.inertClass := hc
    rw [h2] at hc'
    cases hc'
  have hcop : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hp2
  refine ⟨hcop, ?_⟩
  have hN : ¬ p ∣ D.host.condN := Formalism.BasicNotions.not_dvd_conductor_of_inert hp (show D.host.cls p = PrimeClass.inertClass from hc)
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  obtain ⟨P, hPm, hPl⟩ : ∃ P : Ideal (𝓞 D.host.E), P.IsMaximal ∧ P.LiesOver (Ideal.span {(p : ℤ)}) := by
    first
    | exact Ideal.exists_maximal_ideal_liesOver_of_isIntegral _
    | exact Ideal.exists_maximal_ideal_liesOver_of_isIntegral _ _
    | exact Ideal.exists_ideal_liesOver_maximal_of_isIntegral _
    | (obtain ⟨Q, hQm, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 D.host.E)
          (Ideal.span {(p : ℤ)}) (by simp)
       exact ⟨Q, hQm, ⟨hQc.symm⟩⟩)
  haveI : P.IsPrime := hPm.isPrime
  obtain ⟨⟨σ, hσ⟩, -, -, -⟩ := D.host.der.frob p hN P
  have hmem : D.host.galE σ ∈ frobSet D p := ⟨P, inferInstance, hPl, σ, hσ, rfl⟩
  obtain ⟨P', hP'p, hP'l, σ', hσ', hgal⟩ := Classical.epsilon_spec ⟨_, hmem⟩
  obtain ⟨-, -, h3, -⟩ := D.host.der.frob p hN P'
  obtain ⟨-, -, v, hv, hvh⟩ := h3 σ' hσ'
  unfold hP
  simp only [Formalism.HC.Frame.iota_iotaInv]
  rw [← hgal, show ZMod.unitOfCoprime p (Nat.Coprime.pow_right (D.R.e + 2) hcop) = v from
    Units.ext (by rw [ZMod.coe_unitOfCoprime, hv])]
  exact hvh

theorem two_readings_of_Frobenius (D : D7) : Formalism.MainNotions.CornerGLContinuity.FrobeniusClassCompatibility D := by
  intro p hp hc
  obtain ⟨h2, hh⟩ := hH_hP D p hp hc
  refine ⟨fun h => ?_, ?_⟩
  · subst h
    exact absurd h2 (by decide)
  unfold Formalism.MainNotions.GlobalTheoryTheory.hOf
  split_ifs with hcond
  rw [Formalism.BasicNotions.iotaH_iotaHInv, ← hh]
  rfl

end Formalism.MainNotions.J

end
end

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.NandDIVb
section
noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions

def RankMj (D : D7) : Prop := ∀ j ∈ SizeData₂.lifts D, Module.finrank ℂ (D.what₂.Mj j) = D.what₂.D0

def ThetaOnto (D : D7) (μ : D.what₂.Tup) : Prop :=
  ∀ j ∈ SizeData₂.lifts D, Function.Surjective (D.what₂.thetaP μ j)

def LocEachLift (D : D7) : Prop := ∀ j ∈ SizeData₂.lifts D, ∃ i : D.nd.Loc, D.nd.j i = j

theorem RankMj_of_MjRank {D : D7} (X : DivX D)
    (h : ∀ j, 1 ≤ j → j ≤ D.R.m → (X.MjH j).rank = D.what₂.D0) : RankMj D :=
  fun j hj => finrank_Mj X j (h j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2)

theorem RankMj_of_isot {D : D7} (hI : Rows.IsotInternal D.what₂) (hR : Rows.IsotRank D.what₂) : RankMj D :=
  fun j hj => finrank_Mj_of_isot D.what₂ hI hR j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2

theorem dZ0_eq_D0_of_rankMj_of_thetaOnto {D : D7} (L : SizeData₂ D) (hM : RankMj D) (h : ThetaOnto D D.what₂.mu0) :
    ∀ j ∈ SizeData₂.lifts D, L.dZ0 j = D.what₂.D0 := by
  intro j hj
  unfold SizeData₂.dZ0
  rw [finrank_Zj_of_injective D.what₂ _ j (thetaT_injective_of_onto D.what₂ _ j (h j hj)), hM j hj]

theorem rank_at_place_eq_of_surjective {D : D7} (L : SizeData₂ D) (hM : RankMj D) (w : D.what₂.places.Pl)
    (h : ThetaOnto D (D.what₂.muTw w)) : ∀ j ∈ SizeData₂.lifts D, L.zeroSpaceRankAtPlace j w = D.what₂.D0 := by
  intro j hj
  unfold SizeData₂.zeroSpaceRankAtPlace
  rw [finrank_Zj_of_injective D.what₂ _ j (thetaT_injective_of_onto D.what₂ _ j (h j hj)), hM j hj]

theorem theta_injective_of_scalars (D : D7) (h42 : Formalism.MainNotions.SumRepresentations.Conclusion42 D) (hI : Rows.IsotInternal D.what₂)
    (i : D.nd.Loc) (hj : D.nd.j i ∈ SizeData₂.lifts D) :
    Function.Injective (D.what₂.thetaT (D.nd.mu i) (D.nd.j i)) := by
  have hj' := Finset.mem_Icc.mp hj
  exact injective_of_scalars (D.what₂.isot (D.nd.j i)) (hI _ hj'.1 hj'.2) _ (D.what₂.thetaP (D.nd.mu i) (D.nd.j i))
    (fun σ hσ => let ⟨lam, h0, hl⟩ := (h42 i σ hσ).1.1; ⟨(lam : ℂ), by exact_mod_cast h0.ne', hl⟩)

theorem rank_at_place_eq_of_scalars {D : D7} (L : SizeData₂ D) (hM : RankMj D) (h42 : Formalism.MainNotions.SumRepresentations.Conclusion42 D)
    (hI : Rows.IsotInternal D.what₂) (i : D.nd.Loc) (hj : D.nd.j i ∈ SizeData₂.lifts D) :
    L.zeroSpaceRankAtPlace (D.nd.j i) (D.nd.w i) = D.what₂.D0 := by
  have h := theta_injective_of_scalars D h42 hI i hj
  unfold SizeData₂.zeroSpaceRankAtPlace
  rw [← D.nd.mu_w i, finrank_Zj_of_injective D.what₂ _ _ h, hM _ hj]

theorem family_rank_eq_of_surjective {eps : ℝ} (Fm : FamP eps)
    (h : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, RankMj (Fm.D x i) ∧ ThetaOnto (Fm.D x i) (Fm.D x i).what₂.mu0) :
    SmallLevelRankEq Fm := by
  obtain ⟨x0, h⟩ := h
  exact ⟨x0, fun x hx i => dZ0_eq_D0_of_rankMj_of_thetaOnto (Fm.L x i) (h x hx i).1 (h x hx i).2⟩

theorem family_rank_eq_of_scalars {eps : ℝ} (Fm : FamP eps)
    (h : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, RankMj (Fm.D x i) ∧ Formalism.MainNotions.SumRepresentations.Conclusion42 (Fm.D x i) ∧
      Rows.IsotInternal (Fm.D x i).what₂ ∧ LocEachLift (Fm.D x i) ∧ Formalism.MainNotions.TwistedPlaces.adm3 (Fm.L x i)) : SmallLevelRankEq Fm := by
  obtain ⟨x0, h⟩ := h
  refine ⟨x0, fun x hx i j hj => ?_⟩
  obtain ⟨hM, h42, hI, hL, h3⟩ := h x hx i
  obtain ⟨a, rfl⟩ := hL j hj
  rw [← h3 _ hj ((Fm.D x i).nd.w a) ((Fm.D x i).nd.w_tw a)]
  exact rank_at_place_eq_of_scalars (Fm.L x i) hM h42 hI a hj

theorem rank_uniform_over_places {D : D7} (L : SizeData₂ D) (hM : RankMj D) (h : ∀ μ, ThetaOnto D μ) : Formalism.MainNotions.TwistedPlaces.adm3 L := by
  intro j hj w _
  rw [rank_at_place_eq_of_surjective L hM w (h _) j hj, dZ0_eq_D0_of_rankMj_of_thetaOnto L hM (h _) j hj]

end Formalism.MainNotions.J

end
end

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLd
section
noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.MainNotions.PrimeDegreeVariant

theorem del_int {N : ℕ} (lam : DomWeight N) :
    ∀ f0 ∈ delSq ℤ N lam, MvPolynomial.map (Int.castRingHom ℂ) f0 ∈ delSq ℂ N lam := by
  intro f0 hf0
  unfold delSq Formalism.GradedWeylDivisibility.weyl at hf0 ⊢
  induction hf0 using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    refine Submodule.subset_span ⟨w, ?_⟩
    simp only
    rw [← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hx

theorem natW_anti {N : ℕ} (lam : DomWeight N) : Antitone lam.natW := by
  intro i j hij
  have := lam.anti hij
  simp only [DomWeight.natW]
  omega

theorem del_eq_nabla {N : ℕ} (lam : DomWeight N) : delSq ℂ N lam = nablaSq ℂ N lam := by
  apply le_antisymm
  · exact Formalism.GradedWeylDivisibility.weylLeDual ℂ N N le_rfl lam.natW (natW_anti lam)
  · unfold nablaSq
    rw [Formalism.GradedWeylDivisibility.standardMonomialSpanDomain ℂ N N lam.natW, Submodule.span_le]
    rintro _ ⟨K, sz, hsz, I, hsh, rfl⟩
    have h1 : Formalism.GradedWeylDivisibility.bideterminant ℤ sz hsz I ∈ Formalism.GradedWeylDivisibility.dualWeyl ℤ N N lam.natW :=
      hsh ▸ Formalism.GradedWeylDivisibility.bidetMem ℤ N N K sz hsz I
    obtain ⟨c, hc, h2⟩ := Formalism.GradedWeylDivisibility.weylRational N N le_rfl lam.natW (natW_anti lam) _ h1
    have h3 := del_int lam _ h2
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul,
      Formalism.GradedWeylDivisibility.ldlat_map_bidet] at h3
    have hc' : ((Int.castRingHom ℂ) c) ≠ 0 := by simpa using hc
    have h4 := Submodule.smul_mem (delSq ℂ N lam) ((Int.castRingHom ℂ) c)⁻¹ h3
    rwa [smul_smul, inv_mul_cancel₀ hc', one_smul] at h4

theorem del_stable {N : ℕ} (lam : DomWeight N) :
    ∀ g : GL (Fin N) ℂ, ∀ f ∈ delSq ℂ N lam, sqAct ℂ N lam g f ∈ delSq ℂ N lam := by
  intro g f hf
  rw [del_eq_nabla] at hf ⊢
  exact Submodule.smul_mem _ _ (Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ N N lam.natW _ f hf)

theorem isBr_congr {n N : ℕ} {h : n + 1 = N} {lam : DomWeight N} {sg : DomWeight n}
    {br br' : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ}
    (hbr : IsBr h lam sg br) (e : Set.EqOn br' br (delSq ℂ N lam : Set _)) :
    IsBr h lam sg br' := by
  obtain ⟨h1, h2, ⟨f3, hf3, h3⟩, h4, h5, h6⟩ := hbr
  have e1 : ∀ f ∈ delSq ℂ N lam, br' f = br f := fun f hf => e hf
  have e2 : ∀ f0 ∈ delSq ℤ N lam, br' (MvPolynomial.map (Int.castRingHom ℂ) f0) =
      br (MvPolynomial.map (Int.castRingHom ℂ) f0) := fun f0 hf => e (del_int lam f0 hf)
  have e3 : ∀ (g : GL (Fin n) ℂ), ∀ f0 ∈ delSq ℂ N lam, br' (sqAct ℂ N lam (embGL ℂ n N h g) f0) =
      br (sqAct ℂ N lam (embGL ℂ n N h g) f0) := fun g f0 hf => e (del_stable lam _ f0 hf)
  have e4 : ∀ (a : ℂˣ), ∀ f0 ∈ delSq ℂ N lam, br' (sqAct ℂ N lam (lastGL ℂ N a) f0) =
      br (sqAct ℂ N lam (lastGL ℂ N a) f0) := fun a f0 hf => e (del_stable lam _ f0 hf)
  refine ⟨fun f hf => ?_, fun f hf => ?_, ⟨f3, hf3, ?_⟩, fun g f hf => ?_, fun a f hf => ?_, fun f hf => ?_⟩
  · rw [e2 f hf]; exact h1 f hf
  · rw [e1 f hf]; exact h2 f hf
  · rw [e1 f3 hf3]; exact h3
  · rw [e3 g f hf, e1 f hf]; exact h4 g f hf
  · rw [e4 a f hf, e1 f hf]; exact h5 a f hf
  · rw [e1 f hf]; exact h6 f hf

variable {D : D7} {u : D.what₂.Word}

def BrTie (P : product_first_zeroth_parts.Pend D u) : Prop :=
  ∀ τ io br, IsIota (product_first_zeroth_parts.Nm_succ D.R) (product_first_zeroth_parts.lamTr D u τ) (product_first_zeroth_parts.sgTr D u τ) io →
    IsBr (product_first_zeroth_parts.Nm_succ D.R) (product_first_zeroth_parts.lamTr D u τ) (product_first_zeroth_parts.sgTr D u τ) br →
    IsTranspose (product_first_zeroth_parts.lamTr D u τ) (product_first_zeroth_parts.sgTr D u τ) io br →
    Set.EqOn (P.br τ) br (delSq ℂ _ (product_first_zeroth_parts.lamTr D u τ) : Set _)

theorem pending_condition_of_sixth (P : product_first_zeroth_parts.Pend D u) (H : PrimeDegreeVariant.Conclusion6) (tie : BrTie P) : product_first_zeroth_parts.ArchimedeanSignatureMatching P := by
  intro τ
  obtain ⟨-, -, -, -, io, br, hio, hbr, htr⟩ :=
    H _ _ (product_first_zeroth_parts.Nm_succ D.R) (product_first_zeroth_parts.lamTr D u τ) (product_first_zeroth_parts.sgTr D u τ) (product_first_zeroth_parts.interlaceTr D u P.interlace τ)
  exact isBr_congr hbr (tie τ io br hio hbr htr)

end Formalism.MainNotions.J

end
end

